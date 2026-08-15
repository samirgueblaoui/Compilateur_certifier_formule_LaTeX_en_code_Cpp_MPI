#include "formexec_config.hpp"

#include <algorithm>
#include <cctype>
#include <cmath>
#include <fstream>
#include <iomanip>
#include <nlohmann/json.hpp>
#include <optional>
#include <sstream>
#include <stdexcept>

namespace {

using json = nlohmann::json;

// Charge le contenu brut du fichier de configuration.
std::string lireConfig(const std::filesystem::path& chemin) {
    std::ifstream entree(chemin);
    if (!entree.is_open()) {
        throw std::runtime_error("Impossible d'ouvrir le fichier: " + chemin.string());
    }
    std::ostringstream tampon;
    tampon << entree.rdbuf();
    return tampon.str();
}

// Convertit un nombre JSON en scalaire typé pour le compilateur.
ValScalaire versValScalaire(const json& val) {
    if (!val.is_number()) {
        throw std::runtime_error("Valeur non numerique non supportee pour FormExec");
    }

    ValScalaire res;
    double nombre = val.get<double>();
    double entProche = std::round(nombre);
    if (std::abs(nombre - entProche) < 1e-9) {
        res.type = Type::Ent;
        res.texte = std::to_string(static_cast<int>(entProche));
    } else {
        res.type = Type::Flot;
        std::ostringstream flux;
        flux << std::setprecision(17) << nombre;
        res.texte = flux.str();
    }
    return res;
}

// Construit une valeur vectorielle à partir de scalaires.
ValScalaire creerValVecteur(const std::vector<ValScalaire>& elems) {
    ValScalaire res;
    res.type = Type::VectEnt;

    std::ostringstream texte;
    texte << "{";
    for (std::size_t i = 0; i < elems.size(); ++i) {
        if (elems[i].type != Type::Ent && elems[i].type != Type::Flot) {
            throw std::runtime_error("Un vecteur ne peut contenir que des nombres");
        }
        if (elems[i].type == Type::Flot) {
            res.type = Type::VectFlot;
        }
        if (i != 0) {
            texte << ", ";
        }
        texte << elems[i].texte;
    }
    texte << "}";
    res.texte = texte.str();
    return res;
}

// Convertit un tableau JSON en valeur vectorielle.
ValScalaire vecteurDepuisJson(const json& vals) {
    if (!vals.is_array()) {
        throw std::runtime_error("Le champ values d'un vecteur doit etre un tableau numerique");
    }

    std::vector<ValScalaire> elems;
    elems.reserve(vals.size());
    for (const json& val : vals) {
        elems.push_back(versValScalaire(val));
    }
    return creerValVecteur(elems);
}

// Renvoie une copie du texte en minuscules.
std::string copieMinuscule(std::string texte) {
    // Convertit chaque caractère en minuscule.
    std::transform(texte.begin(), texte.end(), texte.begin(), [](unsigned char c) {
        return static_cast<char>(std::tolower(c));
    });
    return texte;
}

// Découpe une ligne en mots séparés par des espaces.
std::vector<std::string> decouperMots(const std::string& ligne) {
    std::istringstream entree(ligne);
    std::vector<std::string> mots;
    std::string mot;
    while (entree >> mot) {
        mots.push_back(mot);
    }
    return mots;
}

// Convertit un mot du fichier vectoriel en scalaire.
ValScalaire scalaireDepuisTexte(const std::string& mot, const std::filesystem::path& chemin) {
    try {
        std::size_t nbLu = 0;
        double nombre = std::stod(mot, &nbLu);
        if (nbLu != mot.size()) {
            throw std::runtime_error("");
        }
        return versValScalaire(json(nombre));
    } catch (...) {
        throw std::runtime_error(
            "Valeur numerique invalide dans le fichier vectoriel " + chemin.string() + ": " + mot
        );
    }
}

// Lit une taille dans le fichier vectoriel.
std::size_t lireTaille(const std::string& mot, const std::filesystem::path& chemin) {
    try {
        std::size_t nbLu = 0;
        unsigned long long val = std::stoull(mot, &nbLu);
        if (nbLu != mot.size()) {
            throw std::runtime_error("");
        }
        return static_cast<std::size_t>(val);
    } catch (...) {
        throw std::runtime_error("Dimension invalide dans le fichier vectoriel: " + chemin.string());
    }
}

// Cherche la prochaine ligne de données du fichier vectoriel.
std::size_t prochaineLigne(
    const std::vector<std::string>& lignes,
    std::size_t debut,
    const std::filesystem::path& chemin
) {
    for (std::size_t i = debut; i < lignes.size(); ++i) {
        std::string texte = lignes[i];
        // Ignore les espaces placés au début de la ligne.
        texte.erase(texte.begin(), std::find_if(texte.begin(), texte.end(), [](unsigned char c) {
            return !std::isspace(c);
        }));
        if (!texte.empty() && texte.front() != '%') {
            return i;
        }
    }
    throw std::runtime_error("Donnees manquantes dans le fichier vectoriel: " + chemin.string());
}

// Lit un vecteur au format MatrixMarket.
ValScalaire lireVecteurMatrix(
    const std::vector<std::string>& lignes,
    const std::filesystem::path& chemin
) {
    const std::vector<std::string> entete = decouperMots(lignes.front());
    if (entete.size() < 5) {
        throw std::runtime_error("En-tete MatrixMarket incomplet: " + chemin.string());
    }

    const std::string nature = copieMinuscule(entete[1]);
    const std::string stockage = copieMinuscule(entete[2]);
    const std::string champ = copieMinuscule(entete[3]);
    if (nature != "vector" && nature != "covector" && nature != "matrix") {
        throw std::runtime_error("Le fichier n'est pas un vecteur MatrixMarket: " + chemin.string());
    }
    if (stockage != "array" && stockage != "coordinate") {
        throw std::runtime_error("Format MatrixMarket vectoriel non supporte: " + stockage);
    }
    if (champ != "integer" && champ != "real") {
        throw std::runtime_error("Seuls les vecteurs MatrixMarket integer/real sont supportes");
    }

    const std::size_t ligneDims = prochaineLigne(lignes, 1, chemin);
    const std::vector<std::string> dims = decouperMots(lignes[ligneDims]);
    std::size_t tailleVect = 0;
    std::size_t nbNonNuls = 0;
    bool vectLigne = false;

    if (nature == "matrix") {
        if (dims.size() < (stockage == "coordinate" ? 3U : 2U)) {
            throw std::runtime_error("Dimensions MatrixMarket invalides: " + chemin.string());
        }
        const std::size_t nbLignes = lireTaille(dims[0], chemin);
        const std::size_t nbColonnes = lireTaille(dims[1], chemin);
        if (nbLignes != 1 && nbColonnes != 1) {
            throw std::runtime_error("Le fichier contient une matrice, pas un vecteur: " + chemin.string());
        }
        vectLigne = nbLignes == 1;
        tailleVect = std::max(nbLignes, nbColonnes);
        nbNonNuls = stockage == "coordinate" ? lireTaille(dims[2], chemin) : tailleVect;
    } else {
        if (dims.empty() || (stockage == "coordinate" && dims.size() < 2)) {
            throw std::runtime_error("Dimensions vectorielles invalides: " + chemin.string());
        }
        tailleVect = lireTaille(dims[0], chemin);
        nbNonNuls = stockage == "coordinate" ? lireTaille(dims[1], chemin) : tailleVect;
    }

    std::vector<ValScalaire> elems(tailleVect, versValScalaire(json(0)));
    std::size_t iLigne = ligneDims + 1;
    for (std::size_t iEntree = 0; iEntree < nbNonNuls; ++iEntree) {
        iLigne = prochaineLigne(lignes, iLigne, chemin);
        const std::vector<std::string> mots = decouperMots(lignes[iLigne]);
        ++iLigne;

        if (stockage == "array") {
            if (mots.empty()) {
                throw std::runtime_error("Valeur vectorielle manquante: " + chemin.string());
            }
            elems[iEntree] = scalaireDepuisTexte(mots[0], chemin);
            continue;
        }

        std::size_t indice = 0;
        std::string motVal;
        if (nature == "matrix") {
            if (mots.size() < 3) {
                throw std::runtime_error("Entree MatrixMarket coordinate invalide: " + chemin.string());
            }
            const std::size_t ligne = lireTaille(mots[0], chemin);
            const std::size_t colonne = lireTaille(mots[1], chemin);
            indice = vectLigne ? colonne : ligne;
            motVal = mots[2];
        } else {
            if (mots.size() < 2) {
                throw std::runtime_error("Entree vectorielle coordinate invalide: " + chemin.string());
            }
            indice = lireTaille(mots[0], chemin);
            motVal = mots[1];
        }
        if (indice == 0 || indice > tailleVect) {
            throw std::runtime_error("Indice MatrixMarket hors limites: " + chemin.string());
        }
        elems[indice - 1] = scalaireDepuisTexte(motVal, chemin);
    }

    return creerValVecteur(elems);
}

// Lit un fichier contenant un vecteur.
ValScalaire lireFichierVecteur(const std::filesystem::path& chemin) {
    std::ifstream entree(chemin);
    if (!entree.is_open()) {
        throw std::runtime_error("Impossible d'ouvrir le fichier vectoriel: " + chemin.string());
    }

    std::vector<std::string> lignes;
    std::string ligne;
    while (std::getline(entree, ligne)) {
        lignes.push_back(ligne);
    }
    if (lignes.empty()) {
        return creerValVecteur({});
    }

    if (copieMinuscule(lignes.front()).starts_with("%%matrixmarket")) {
        return lireVecteurMatrix(lignes, chemin);
    }

    std::vector<ValScalaire> elems;
    for (std::string courante : lignes) {
        const std::size_t commentaire = courante.find_first_of("#%");
        if (commentaire != std::string::npos) {
            courante.erase(commentaire);
        }
        std::replace(courante.begin(), courante.end(), ',', ' ');
        for (const std::string& mot : decouperMots(courante)) {
            elems.push_back(scalaireDepuisTexte(mot, chemin));
        }
    }
    return creerValVecteur(elems);
}

// Indique si une valeur JSON décrit un vecteur.
bool estDescrVecteur(const json& val) {
    return val.is_object() && (val.contains("values") || val.contains("file"));
}

// Convertit un descripteur JSON en valeur vectorielle.
ValScalaire versValVecteur(const json& descr, const std::filesystem::path& dossierConfig) {
    if (!estDescrVecteur(descr)) {
        throw std::runtime_error("Descripteur de vecteur invalide");
    }

    if (descr.contains("values")) {
        return vecteurDepuisJson(descr.at("values"));
    }

    const json& fichier = descr.at("file");
    if (!fichier.is_string()) {
        throw std::runtime_error("Le champ file d'un vecteur doit etre une chaine");
    }
    if (descr.contains("reading") && !descr.at("reading").is_string()) {
        throw std::runtime_error("Le champ reading d'un vecteur doit etre une chaine");
    }

    std::filesystem::path cheminVect = fichier.get<std::string>();
    if (cheminVect.is_relative()) {
        cheminVect = dossierConfig / cheminVect;
    }
    ValScalaire res;
    res.type = Type::VectFlot;
    res.texte = "{}";
    res.fichierSrc = cheminVect.lexically_normal();
    return res;
}

// Récupère un champ obligatoire d'un objet JSON.
const json& champObligatoire(const json& objet, const std::string& cle) {
    auto it = objet.find(cle);
    if (it == objet.end()) {
        throw std::runtime_error("Champ JSON manquant: " + cle);
    }
    return *it;
}

// Écrase les constantes du modèle de coût avec celles du JSON.
void appliquerOptsSommes(const json& val, OptsStrSom& opts) {
    if (!val.is_object()) {
        throw std::runtime_error("sumStrategy doit etre un objet JSON");
    }

    // Applique une option flottante.
    auto appliquerFlot = [&](const char* cle, double& cible) {
        auto it = val.find(cle);
        if (it != val.end()) {
            if (!it->is_number()) {
                throw std::runtime_error(std::string("sumStrategy.") + cle + " doit etre numerique");
            }
            cible = it->get<double>();
        }
    };

    // Applique une option entière.
    auto appliquerEnt = [&](const char* cle, int& cible) {
        auto it = val.find(cle);
        if (it != val.end()) {
            if (!it->is_number_integer() && !it->is_number_unsigned()) {
                throw std::runtime_error(std::string("sumStrategy.") + cle + " doit etre entier");
            }
            cible = it->get<int>();
        }
    };

    appliquerFlot("unaryDefaultCost", opts.coutFoncUnaireDef);
    appliquerFlot("binaryDefaultCost", opts.coutFoncBinDef);
    appliquerFlot("arithmeticBinaryCost", opts.coutOpArith);
    appliquerFlot("accumulatorCost", opts.coutAcc);
    appliquerFlot("communicationCost", opts.coutCom);
    appliquerFlot("synchronizationCost", opts.coutSynchro);
    appliquerEnt("assumedProcesses", opts.nbProc);
    appliquerEnt("minParallelIterations", opts.minIterPar);
    appliquerEnt("unknownIntervalFallback", opts.tailleIntervDef);
    appliquerEnt("nestedGroups", opts.nbGrpImb);
    appliquerFlot("reductionVolume", opts.volReduc);
}

// Lit un coût numérique quand sa forme est valide.
std::optional<double> lireCoutNum(const json& val) {
    if (val.is_number()) {
        return val.get<double>();
    }
    if (val.is_string()) {
        const std::string texte = val.get<std::string>();
        try {
            std::size_t nbLu = 0;
            double nombre = std::stod(texte, &nbLu);
            if (nbLu == texte.size()) {
                return nombre;
            }
        } catch (...) {
        }
    }
    return std::nullopt;
}

// Charge les liaisons de fonctions définies dans le JSON.
std::vector<LiaisonFonc> chargerLiaisonsFoncs(const json& racine, OptsStrSom& opts) {
    std::vector<LiaisonFonc> liaisons;

    auto itFoncs = racine.find("functions");
    if (itFoncs == racine.end()) {
        return liaisons;
    }
    if (!itFoncs->is_array()) {
        throw std::runtime_error("config.json invalide: functions n'est pas un tableau");
    }

    for (const json& fonc : *itFoncs) {
        if (!fonc.is_object()) {
            continue;
        }

        auto itLatex = fonc.find("latex");
        auto itCpp = fonc.find("c++");
        auto itType = fonc.find("type");
        if (itLatex == fonc.end() || itCpp == fonc.end() || itType == fonc.end()) {
            continue;
        }
        if (!itLatex->is_string() || !itCpp->is_string() || !itType->is_object()) {
            continue;
        }

        auto itEntrees = itType->find("input");
        if (itEntrees == itType->end() || !itEntrees->is_array()) {
            continue;
        }

        LiaisonFonc liaison;
        liaison.nomLatex = itLatex->get<std::string>();
        liaison.nomCpp = itCpp->get<std::string>();
        liaison.arite = static_cast<int>(itEntrees->size());

        auto itCout = itType->find("cost");
        if (itCout != itType->end()) {
            if (itCout->is_object()) {
                auto itCoutCpp = itCout->find("c++");
                if (itCoutCpp != itCout->end()) {
                    liaison.coutNum = lireCoutNum(*itCoutCpp);
                    if (itCoutCpp->is_string()) {
                        liaison.coutBrut = itCoutCpp->get<std::string>();
                    }
                }
            } else {
                liaison.coutNum = lireCoutNum(*itCout);
                if (itCout->is_string()) {
                    liaison.coutBrut = itCout->get<std::string>();
                }
            }
        }

        if (liaison.coutNum.has_value()) {
            if (liaison.arite == 1) {
                opts.coutsFoncsUnaires[liaison.nomLatex] = *liaison.coutNum;
            } else if (liaison.arite == 2) {
                opts.coutsFoncsBin[liaison.nomLatex] = *liaison.coutNum;
            }
        }

        liaisons.push_back(liaison);
    }

    return liaisons;
}

} // namespace

// Matérialise un vecteur référencé par un fichier.
ValScalaire resoudreValFichier(const ValScalaire& val) {
    if (!val.fichierSrc.has_value()) {
        return val;
    }
    return lireFichierVecteur(*val.fichierSrc);
}

// Lit la configuration et renvoie la section demandée.
DonneesSection chargerSection(const std::filesystem::path& cheminConfig, int section) {
    json racine = json::parse(lireConfig(cheminConfig));
    if (!racine.is_object()) {
        throw std::runtime_error("config.json invalide: racine non objet");
    }

    OptsStrSom optsGlobales;
    auto itStrategieGlobale = racine.find("sumStrategy");
    if (itStrategieGlobale != racine.end()) {
        appliquerOptsSommes(*itStrategieGlobale, optsGlobales);
    }
    std::vector<LiaisonFonc> liaisonsGlobales = chargerLiaisonsFoncs(racine, optsGlobales);

    const json& environnements = champObligatoire(racine, "environments");
    if (!environnements.is_array()) {
        throw std::runtime_error("config.json invalide: environments n'est pas un tableau");
    }

    for (const json& environnement : environnements) {
        if (!environnement.is_object()) {
            continue;
        }
        auto itSection = environnement.find("section");
        if (itSection == environnement.end() || !itSection->is_number()) {
            continue;
        }
        if (static_cast<int>(std::round(itSection->get<double>())) != section) {
            continue;
        }

        DonneesSection donnees;
        const std::filesystem::path dossierConfig = cheminConfig.parent_path();
        donnees.optsSommes = optsGlobales;
        donnees.liaisonsFoncs = liaisonsGlobales;
        for (auto it = environnement.begin(); it != environnement.end(); ++it) {
            const std::string cle = it.key();
            const json& val = it.value();
            if (cle == "section") {
                continue;
            }

            if (cle == "sumStrategy") {
                appliquerOptsSommes(val, donnees.optsSommes);
                continue;
            }

            if (cle == "processors") {
                if (!val.is_array()) {
                    throw std::runtime_error("processors doit etre un tableau");
                }
                donnees.procs.clear();
                for (const json& elem : val) {
                    if (!elem.is_number()) {
                        throw std::runtime_error("processors contient une valeur non numerique");
                    }
                    donnees.procs.push_back(static_cast<int>(std::round(elem.get<double>())));
                }
                if (donnees.procs.empty()) {
                    donnees.procs.push_back(1);
                }
                continue;
            }

            if (val.is_number()) {
                donnees.varsFixes[cle] = versValScalaire(val);
                continue;
            }

            if (estDescrVecteur(val)) {
                donnees.varsFixes[cle] = versValVecteur(val, dossierConfig);
                continue;
            }

            if (val.is_array()) {
                std::vector<ValScalaire> vals;
                bool tousNombres = true;
                for (const json& elem : val) {
                    if (!elem.is_number()) {
                        tousNombres = false;
                        break;
                    }
                    vals.push_back(versValScalaire(elem));
                }
                if (tousNombres) {
                    donnees.varsMulti.push_back({cle, vals});
                    continue;
                }

                bool tousVecteurs = !val.empty();
                vals.clear();
                for (const json& elem : val) {
                    if (!estDescrVecteur(elem)) {
                        tousVecteurs = false;
                        break;
                    }
                    vals.push_back(versValVecteur(elem, dossierConfig));
                }
                if (tousVecteurs) {
                    donnees.varsMulti.push_back({cle, vals});
                }
            }
        }

        if (!donnees.varsMulti.empty()) {
            std::size_t tailleAttendue = donnees.varsMulti.front().second.size();
            for (const auto& [nom, vals] : donnees.varsMulti) {
                if (vals.size() != tailleAttendue) {
                    throw std::runtime_error(
                        "Toutes les listes numeriques d'une section MULTI doivent avoir la meme taille: " + nom
                    );
                }
            }
        }

        return donnees;
    }

    throw std::runtime_error("Section introuvable dans config.json: " + std::to_string(section));
}
