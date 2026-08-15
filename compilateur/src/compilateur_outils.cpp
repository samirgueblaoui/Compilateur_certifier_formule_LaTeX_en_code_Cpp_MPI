#include "compilateur_outils.hpp"

#include <cctype>
#include <optional>
#include <set>
#include <stdexcept>

namespace compilateur_outils {

namespace {

// Transforme un nom en identifiant C++.
std::string nettoyerNom(const std::string& nom) {
    if (nom == "\\sin") return "sin";
    if (nom == "\\cos") return "cos";
    if (nom == "\\tan") return "tan";
    if (nom == "/") return "div";
    if (nom == "^") return "pow";
    if (nom == "-") return "neg";
    if (nom == "+") return "add";
    if (nom == "*") return "mul";
    if (nom == "=") return "eq";
    if (nom == "<") return "lt";
    if (nom == ">") return "gt";

    std::string sortie;
    sortie.reserve(nom.size());
    for (char car : nom) {
        if (std::isalnum(static_cast<unsigned char>(car)) || car == '_') {
            sortie.push_back(car);
        } else if (car == '\\') {
            continue;
        } else {
            sortie.push_back('_');
        }
    }

    if (sortie.empty()) {
        return "op";
    }

    if (std::isdigit(static_cast<unsigned char>(sortie.front()))) {
        sortie.insert(sortie.begin(), '_');
    }

    return sortie;
}

// Recense les fonctions présentes dans une expression.
void recenserFoncs(
    const ExprPtr& expr,
    std::set<std::string>& foncsUnaires,
    std::set<std::string>& foncsBinaires
) {
    if (auto fonc = std::dynamic_pointer_cast<FoncUnaire>(expr)) {
        foncsUnaires.insert(fonc->nom);
        recenserFoncs(fonc->arg, foncsUnaires, foncsBinaires);
        return;
    }

    if (auto exprBin = std::dynamic_pointer_cast<ExprBin>(expr)) {
        if (exprBin->op != "+" && exprBin->op != "*" &&
            exprBin->op != "-" && exprBin->op != "/") {
            foncsBinaires.insert(exprBin->op);
        }
        recenserFoncs(exprBin->gch, foncsUnaires, foncsBinaires);
        recenserFoncs(exprBin->drt, foncsUnaires, foncsBinaires);
        return;
    }

    if (auto acces = std::dynamic_pointer_cast<AccesVecteur>(expr)) {
        recenserFoncs(acces->vecteur, foncsUnaires, foncsBinaires);
        recenserFoncs(acces->indice, foncsUnaires, foncsBinaires);
        return;
    }

    if (auto somme = std::dynamic_pointer_cast<Somme>(expr)) {
        recenserFoncs(somme->bInf, foncsUnaires, foncsBinaires);
        recenserFoncs(somme->bSup, foncsUnaires, foncsBinaires);
        recenserFoncs(somme->corps, foncsUnaires, foncsBinaires);
    }
}

// Ajoute les signatures d'une fonction unaire.
void ajouterSigUnaire(const std::string& nom, EnvFoncs& foncs) {
    if (nom == "EuclideanNorm") {
        foncs[nom].push_back({Type::Ent, Type::Ent});
        foncs[nom].push_back({Type::Flot, Type::Flot});
        foncs[nom].push_back({Type::VectEnt, Type::Flot});
        foncs[nom].push_back({Type::VectFlot, Type::Flot});
        return;
    }

    if (nom == "FrobeniusNorm") {
        foncs[nom].push_back({Type::VectEnt, Type::Flot});
        foncs[nom].push_back({Type::VectFlot, Type::Flot});
        return;
    }

    foncs[nom].push_back({Type::Flot, Type::Flot});
}

// Ajoute les signatures d'une fonction binaire.
void ajouterSigBin(const std::string& nom, EnvFoncsBin& foncsBin) {
    if (nom == "/") {
        foncsBin[nom].push_back({Type::Ent, Type::Ent, Type::Flot});
        foncsBin[nom].push_back({Type::Flot, Type::Flot, Type::Flot});
        foncsBin[nom].push_back({Type::Flot, Type::Ent, Type::Flot});
        foncsBin[nom].push_back({Type::Ent, Type::Flot, Type::Flot});
        return;
    }

    if (nom == "^") {
        foncsBin[nom].push_back({Type::Ent, Type::Ent, Type::Ent});
        foncsBin[nom].push_back({Type::Flot, Type::Ent, Type::Flot});
        foncsBin[nom].push_back({Type::Flot, Type::Flot, Type::Flot});
        foncsBin[nom].push_back({Type::Ent, Type::Flot, Type::Flot});
        return;
    }

    foncsBin[nom].push_back({Type::Flot, Type::Flot, Type::Flot});
}

// Recense les variables qui doivent avoir un type donné.
void recenserVarsType(
    const ExprPtr& expr,
    Env& env,
    Type type,
    const std::set<std::string>& varsLiees
) {
    if (auto var = std::dynamic_pointer_cast<Var>(expr)) {
        if (varsLiees.contains(var->nom)) {
            return;
        }
        auto pos = env.find(var->nom);
        if (pos == env.end() || pos->second != Type::Ent) {
            env[var->nom] = type;
        }
        return;
    }

    if (auto fonc = std::dynamic_pointer_cast<FoncUnaire>(expr)) {
        recenserVarsType(fonc->arg, env, type, varsLiees);
        return;
    }

    if (auto exprBin = std::dynamic_pointer_cast<ExprBin>(expr)) {
        recenserVarsType(exprBin->gch, env, type, varsLiees);
        recenserVarsType(exprBin->drt, env, type, varsLiees);
        return;
    }

    if (auto acces = std::dynamic_pointer_cast<AccesVecteur>(expr)) {
        Type typeVect = type == Type::Ent ? Type::VectEnt : Type::VectFlot;
        if (auto var = std::dynamic_pointer_cast<Var>(acces->vecteur)) {
            if (!varsLiees.contains(var->nom)) {
                env[var->nom] = typeVect;
            }
        } else {
            recenserVarsType(acces->vecteur, env, typeVect, varsLiees);
        }
        recenserVarsType(acces->indice, env, Type::Ent, varsLiees);
        return;
    }

    if (auto somme = std::dynamic_pointer_cast<Somme>(expr)) {
        recenserVarsType(somme->bInf, env, type, varsLiees);
        recenserVarsType(somme->bSup, env, type, varsLiees);
        std::set<std::string> varsImb = varsLiees;
        varsImb.insert(somme->ind);
        recenserVarsType(somme->corps, env, type, varsImb);
    }
}

// Infère récursivement les types des variables libres.
void infererEnvRec(
    const ExprPtr& expr,
    Env& env,
    const std::set<std::string>& varsLiees
) {
    if (auto somme = std::dynamic_pointer_cast<Somme>(expr)) {
        recenserVarsType(somme->bInf, env, Type::Ent, varsLiees);
        recenserVarsType(somme->bSup, env, Type::Ent, varsLiees);
        std::set<std::string> varsImb = varsLiees;
        varsImb.insert(somme->ind);
        infererEnvRec(somme->corps, env, varsImb);
        return;
    }

    if (auto var = std::dynamic_pointer_cast<Var>(expr)) {
        if (!varsLiees.contains(var->nom)) {
            env.try_emplace(var->nom, Type::Flot);
        }
        return;
    }

    if (auto fonc = std::dynamic_pointer_cast<FoncUnaire>(expr)) {
        infererEnvRec(fonc->arg, env, varsLiees);
        return;
    }

    if (auto exprBin = std::dynamic_pointer_cast<ExprBin>(expr)) {
        infererEnvRec(exprBin->gch, env, varsLiees);
        infererEnvRec(exprBin->drt, env, varsLiees);
        return;
    }

    if (auto acces = std::dynamic_pointer_cast<AccesVecteur>(expr)) {
        if (auto var = std::dynamic_pointer_cast<Var>(acces->vecteur)) {
            if (!varsLiees.contains(var->nom)) {
                env[var->nom] = Type::VectFlot;
            }
        } else {
            infererEnvRec(acces->vecteur, env, varsLiees);
        }
        recenserVarsType(acces->indice, env, Type::Ent, varsLiees);
    }
}

} // namespace

// Construit les environnements des fonctions utilisées.
void construireEnvFoncs(const ExprPtr& expr, EnvFoncs& foncs, EnvFoncsBin& foncsBin) {
    std::set<std::string> foncsUnaires;
    std::set<std::string> foncsBinaires;
    recenserFoncs(expr, foncsUnaires, foncsBinaires);

    for (const auto& nom : foncsUnaires) {
        ajouterSigUnaire(nom, foncs);
    }

    for (const auto& nom : foncsBinaires) {
        ajouterSigBin(nom, foncsBin);
    }
}

// Infère les types des variables libres.
void infererEnv(const ExprPtr& expr, Env& env) {
    infererEnvRec(expr, env, {});
}

// Convertit un type vers son nom C++.
std::string typeCpp(Type type) {
    switch (type) {
        case Type::Ent: return "int";
        case Type::Flot: return "double";
        case Type::VectEnt: return "std::vector<int>";
        case Type::VectFlot: return "std::vector<double>";
    }
    throw std::runtime_error("Type C++ inconnu");
}

// Convertit un type vers son nom MPI.
std::string typeMpi(Type type) {
    switch (type) {
        case Type::Ent: return "MPI_INT";
        case Type::Flot: return "MPI_DOUBLE";
        case Type::VectEnt:
        case Type::VectFlot:
            throw std::runtime_error("Une reduction MPI scalaire ne peut pas porter sur un vecteur");
    }
    throw std::runtime_error("Type MPI inconnu");
}

// Renvoie la valeur nulle d'un type.
std::string valNulle(Type type) {
    switch (type) {
        case Type::Ent: return "0";
        case Type::Flot: return "0.0";
        case Type::VectEnt:
        case Type::VectFlot: return "{}";
    }
    throw std::runtime_error("Type inconnu pour la valeur nulle");
}

// Renvoie le type commun de deux valeurs.
Type promouvoir(Type typeGch, Type typeDrt) {
    if (estVecteur(typeGch) || estVecteur(typeDrt)) {
        throw std::runtime_error(
            "Les operations arithmetiques sur des vecteurs complets ne sont pas encore supportees; "
            "utilisez un acces v[i]"
        );
    }
    if (typeGch == Type::Flot || typeDrt == Type::Flot) {
        return Type::Flot;
    }

    return Type::Ent;
}

// Indique si un type est vectoriel.
bool estVecteur(Type type) {
    return type == Type::VectEnt || type == Type::VectFlot;
}

// Renvoie le type des éléments d'un vecteur.
Type typeElem(Type type) {
    if (type == Type::VectEnt) {
        return Type::Ent;
    }
    if (type == Type::VectFlot) {
        return Type::Flot;
    }
    throw std::runtime_error("Un acces vectoriel attend un vecteur");
}

// Indique si l'expression contient une somme parallèle.
bool contientSommePar(const ExprPtr& expr) {
    if (auto somme = std::dynamic_pointer_cast<Somme>(expr)) {
        if (somme->nat == NatSomme::Par) {
            return true;
        }

        return contientSommePar(somme->bInf)
            || contientSommePar(somme->bSup)
            || contientSommePar(somme->corps);
    }

    if (auto fonc = std::dynamic_pointer_cast<FoncUnaire>(expr)) {
        return contientSommePar(fonc->arg);
    }

    if (auto exprBin = std::dynamic_pointer_cast<ExprBin>(expr)) {
        return contientSommePar(exprBin->gch) || contientSommePar(exprBin->drt);
    }

    if (auto acces = std::dynamic_pointer_cast<AccesVecteur>(expr)) {
        return contientSommePar(acces->vecteur) || contientSommePar(acces->indice);
    }

    return false;
}

// Construit le nom C++ d'une fonction unaire.
std::string nomFoncUnGen(const std::string& nom) {
    return "genFoncU_" + nettoyerNom(nom);
}

// Construit le nom C++ d'une fonction binaire.
std::string nomFoncBinGen(const std::string& nom) {
    return "genFoncB_" + nettoyerNom(nom);
}

// Construit le corps d'une fonction unaire.
std::string corpsFoncUn(const std::string& nom, Type typeArg, Type typeRes) {
    if ((nom == "EuclideanNorm" || nom == "FrobeniusNorm") && estVecteur(typeArg)) {
        return "std::sqrt(std::inner_product(x.begin(), x.end(), x.begin(), 0.0))";
    }
    if (nom == "EuclideanNorm" && !estVecteur(typeArg)) {
        return "std::abs(x)";
    }
    return "throw std::runtime_error(\"Fonction unaire a completer : " + nom + "\"), " + valNulle(typeRes);
}

// Construit le corps d'une fonction binaire.
std::string corpsFoncBin(const std::string& nom, Type typeRes) {
    return "throw std::runtime_error(\"Fonction binaire a completer : " + nom + "\"), " + valNulle(typeRes);
}

// Indique si deux types sont compatibles.
bool typeCompat(Type obtenu, Type attendu) {
    if (estVecteur(obtenu) || estVecteur(attendu)) {
        return obtenu == attendu;
    }
    return obtenu == attendu || (obtenu == Type::Ent && attendu == Type::Flot);
}

// Cherche une signature binaire compatible.
std::optional<SigFoncBin> trouverSigBin(
    const std::string& nom,
    Type typeGch,
    Type typeDrt,
    const EnvFoncsBin& foncsBin
) {
    auto pos = foncsBin.find(nom);
    if (pos == foncsBin.end()) {
        return std::nullopt;
    }

    for (const auto& sig : pos->second) {
        const auto& [typeGchAtt, typeDrtAtt, typeRes] = sig;
        if (typeCompat(typeGch, typeGchAtt) && typeCompat(typeDrt, typeDrtAtt)) {
            return SigFoncBin{typeGchAtt, typeDrtAtt, typeRes};
        }
    }

    return std::nullopt;
}

// Cherche une signature unaire compatible.
std::optional<SigFoncUnaire> trouverSigUnaire(
    const std::string& nom,
    Type typeArg,
    const EnvFoncs& foncs
) {
    auto pos = foncs.find(nom);
    if (pos == foncs.end()) {
        return std::nullopt;
    }

    for (const auto& sig : pos->second) {
        const auto& [typeArgAtt, typeRes] = sig;
        if (typeCompat(typeArg, typeArgAtt)) {
            return SigFoncUnaire{typeArgAtt, typeRes};
        }
    }

    return std::nullopt;
}

} // namespace compilateur_outils
