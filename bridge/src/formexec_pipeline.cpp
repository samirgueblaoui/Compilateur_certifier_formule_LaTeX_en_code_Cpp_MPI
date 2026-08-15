#include "formexec_pipeline.hpp"

#include "convert_exprlatex_to_compilateur.hpp"
#include "formexec_config.hpp"
#include "parse_exprlatex.hpp"

#include "compilateur.hpp"
#include "compilateur_outils.hpp"

#include <cmath>
#include <fstream>
#include <map>
#include <sstream>
#include <stdexcept>

namespace {

// Convertit les valeurs JSON en valeurs connues.
EnvValsConnues versValsConnues(const std::map<std::string, ValScalaire>& valeurs) {
    EnvValsConnues resultat;
    for (const auto& [nom, val] : valeurs) {
        if (compilateur_outils::estVecteur(val.type)) {
            continue;
        }
        ValConnue connue;
        connue.type = val.type;
        if (val.type == Type::Ent) {
            connue.valEnt = std::stoi(val.texte);
            connue.valFlot = static_cast<double>(connue.valEnt);
        } else {
            connue.valFlot = std::stod(val.texte);
            connue.valEnt = static_cast<int>(std::round(connue.valFlot));
        }
        resultat[nom] = connue;
    }
    return resultat;
}

// Applique les types des vecteurs configurés.
void appliquerTypesVect(const std::map<std::string, ValScalaire>& valeurs, Env& env) {
    for (const auto& [nom, val] : valeurs) {
        if (!compilateur_outils::estVecteur(val.type)) {
            continue;
        }
        auto pos = env.find(nom);
        if (pos != env.end()) {
            pos->second = resoudreValFichier(val).type;
        }
    }
}

// Remplace toutes les occurrences d'un texte.
void remplacerTout(std::string& texte, const std::string& ancien, const std::string& nouveau) {
    if (ancien.empty()) {
        return;
    }
    std::size_t pos = 0;
    while ((pos = texte.find(ancien, pos)) != std::string::npos) {
        texte.replace(pos, ancien.size(), nouveau);
        pos += nouveau.size();
    }
}

// Applique une liaison de fonction au code généré.
void appliquerLiaisonFonc(std::string& code, const LiaisonFonc& liaison) {
    if (liaison.nomCpp.empty()) {
        return;
    }

    if (liaison.arite == 1) {
        remplacerTout(
            code,
            "return throw std::runtime_error(\"Fonction unaire a completer : " + liaison.nomLatex
                + "\"), 0.0; // corps a modifier",
            "return " + liaison.nomCpp + "(x); // corps a modifier"
        );
        remplacerTout(
            code,
            "return throw std::runtime_error(\"Fonction unaire a completer : " + liaison.nomLatex
                + "\"), 0; // corps a modifier",
            "return " + liaison.nomCpp + "(x); // corps a modifier"
        );
    }

    if (liaison.arite == 2) {
        remplacerTout(
            code,
            "return throw std::runtime_error(\"Fonction binaire a completer : " + liaison.nomLatex
                + "\"), 0.0; // corps a modifier",
            "return " + liaison.nomCpp + "(x, y); // corps a modifier"
        );
        remplacerTout(
            code,
            "return throw std::runtime_error(\"Fonction binaire a completer : " + liaison.nomLatex
                + "\"), 0; // corps a modifier",
            "return " + liaison.nomCpp + "(x, y); // corps a modifier"
        );
    }
}

} // namespace

// Lit tout le contenu d'un fichier.
std::string lireFichier(const std::filesystem::path& chemin) {
    std::ifstream entree(chemin);
    if (!entree.is_open()) {
        throw std::runtime_error("Impossible d'ouvrir le fichier: " + chemin.string());
    }
    std::ostringstream tampon;
    tampon << entree.rdbuf();
    return tampon.str();
}

// Écrit tout le contenu d'un fichier.
void ecrireFichier(const std::filesystem::path& chemin, const std::string& contenu) {
    std::ofstream sortie(chemin);
    if (!sortie.is_open()) {
        throw std::runtime_error("Impossible d'ecrire le fichier: " + chemin.string());
    }
    sortie << contenu;
}

// Génère le programme C++ d'une formule.
std::filesystem::path genererProgramme(
    const std::filesystem::path& cheminFormule,
    const std::filesystem::path& cheminCpp,
    const std::map<std::string, ValScalaire>& valeurs,
    const OptsStrSom& optsSom
) {
    std::shared_ptr<ExprNode> astLatex = lireExprLatex(cheminFormule.string());
    ExprPtr expr = convertirExpr(astLatex);
    expr = specialiserSommes(expr, versValsConnues(valeurs), optsSom);

    Env env;
    compilateur_outils::infererEnv(expr, env);
    appliquerTypesVect(valeurs, env);

    EnvFoncs foncs;
    EnvFoncsBin foncsBin;
    compilateur_outils::construireEnvFoncs(expr, foncs, foncsBin);

    Type type = typeDe(expr, env, foncs, foncsBin);
    (void)type;
    std::string programme = compilProg(expr, env, foncs, foncsBin);
    ecrireProg(cheminCpp.string(), programme);
    return cheminCpp;
}

// Complète le code généré avec les valeurs et les fonctions configurées.
std::string completerCodeGenere(
    std::string code,
    const std::map<std::string, ValScalaire>& valeurs,
    const std::vector<LiaisonFonc>& liaisons
) {
    for (const LiaisonFonc& liaison : liaisons) {
        appliquerLiaisonFonc(code, liaison);
    }

    std::istringstream entree(code);
    std::ostringstream sortie;
    std::string ligne;

    while (std::getline(entree, ligne)) {
        std::size_t marqueur = ligne.find("// variable libre a modifier");
        if (marqueur != std::string::npos) {
            std::size_t pointVirgule = ligne.find(';');
            std::size_t egal = ligne.find('=');
            if (pointVirgule != std::string::npos && egal != std::string::npos && egal < pointVirgule) {
                std::string gauche = ligne.substr(0, egal);
                std::istringstream declaration(gauche);
                std::string nomType;
                std::string nomVar;
                declaration >> nomType >> nomVar;
                auto pos = valeurs.find(nomVar);
                if (pos != valeurs.end()) {
                    ValScalaire val = resoudreValFichier(pos->second);
                    sortie << nomType << " " << nomVar << " = " << val.texte
                           << "; // variable libre a modifier\n";
                    continue;
                }
            }
        }
        sortie << ligne << "\n";
    }

    return sortie.str();
}
