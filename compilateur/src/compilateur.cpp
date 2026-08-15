#include "compilateur.hpp"
#include "compilateur_outils.hpp"

#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>

using namespace compilateur_outils;

// AST
// Crée une constante entière.
CstEnt::CstEnt(int v) : val(v) {}

// Crée une constante flottante.
CstFlot::CstFlot(double v) : val(v) {}

// Crée une variable.
Var::Var(std::string n) : nom(std::move(n)) {}

// Crée un appel de fonction unaire.
FoncUnaire::FoncUnaire(std::string f, ExprPtr e)
    : nom(std::move(f)), arg(std::move(e)) {}

// Crée une expression binaire.
ExprBin::ExprBin(std::string opBin, ExprPtr g, ExprPtr d)
    : op(std::move(opBin)), gch(std::move(g)), drt(std::move(d)) {}

// Crée un accès à un vecteur.
AccesVecteur::AccesVecteur(ExprPtr v, ExprPtr i)
    : vecteur(std::move(v)), indice(std::move(i)) {}

// Crée une somme.
Somme::Somme(NatSomme n, std::string i, ExprPtr a, ExprPtr b, ExprPtr e)
    : nat(n),
      ind(std::move(i)),
      bInf(std::move(a)),
      bSup(std::move(b)),
      corps(std::move(e)) {}

// Détermine le type d'une expression.
Type typeDe(const ExprPtr& expr, Env env, const EnvFoncs& foncs, const EnvFoncsBin& foncsBin) {
    if (std::dynamic_pointer_cast<CstEnt>(expr)) {
        return Type::Ent;
    }

    if (std::dynamic_pointer_cast<CstFlot>(expr)) {
        return Type::Flot;
    }

    if (auto var = std::dynamic_pointer_cast<Var>(expr)) {
        if (!env.contains(var->nom)) {
            throw std::runtime_error("Variable non définie : " + var->nom);
        }

        return env[var->nom];
    }

    if (auto fonc = std::dynamic_pointer_cast<FoncUnaire>(expr)) {
        if (!foncs.contains(fonc->nom)) {
            throw std::runtime_error("Fonction non définie : " + fonc->nom);
        }

        Type typeArg = typeDe(fonc->arg, env, foncs, foncsBin);
        auto sigOpt = trouverSigUnaire(fonc->nom, typeArg, foncs);
        if (!sigOpt.has_value()) {
            throw std::runtime_error("Mauvais type pour l'argument de " + fonc->nom);
        }
        return sigOpt->second;
    }

    if (auto exprBin = std::dynamic_pointer_cast<ExprBin>(expr)) {
        Type typeGch = typeDe(exprBin->gch, env, foncs, foncsBin);
        Type typeDrt = typeDe(exprBin->drt, env, foncs, foncsBin);
        if (exprBin->op == "+" || exprBin->op == "*" || exprBin->op == "-") {
            return promouvoir(typeGch, typeDrt);
        }
        if (exprBin->op == "/") {
            if (estVecteur(typeGch) || estVecteur(typeDrt)) {
                throw std::runtime_error("La division de vecteurs complets n'est pas supportee");
            }
            return Type::Flot;
        }
        auto sigOpt = trouverSigBin(exprBin->op, typeGch, typeDrt, foncsBin);
        if (!sigOpt.has_value()) {
            throw std::runtime_error("Fonction binaire non définie : " + exprBin->op);
        }
        return std::get<2>(*sigOpt);
    }

    if (auto acces = std::dynamic_pointer_cast<AccesVecteur>(expr)) {
        Type typeVecteur = typeDe(acces->vecteur, env, foncs, foncsBin);
        Type typeIndice = typeDe(acces->indice, env, foncs, foncsBin);
        if (!estVecteur(typeVecteur)) {
            throw std::runtime_error("Un acces v[i] attend un vecteur a gauche");
        }
        if (typeIndice != Type::Ent) {
            throw std::runtime_error("L'indice d'un vecteur doit etre de type Int");
        }
        return typeElem(typeVecteur);
    }

    if (auto somme = std::dynamic_pointer_cast<Somme>(expr)) {
        Type typeBInf = typeDe(somme->bInf, env, foncs, foncsBin);
        Type typeBSup = typeDe(somme->bSup, env, foncs, foncsBin);

        if (typeBInf != Type::Ent || typeBSup != Type::Ent) {
            throw std::runtime_error("Les bornes d'une somme doivent être de type Int");
        }

        Env envLoc = env;
        envLoc[somme->ind] = Type::Ent;

        Type typeCorps = typeDe(somme->corps, envLoc, foncs, foncsBin);

        if (estVecteur(typeCorps)) {
            throw std::runtime_error("Une somme de vecteurs complets n'est pas encore supportee");
        }

        if (somme->nat == NatSomme::Par && typeCorps == Type::Flot) {
            std::cerr
                << "Avertissement : somme parallèle sur Float, "
                << "résultat potentiellement différent du séquentiel.\n";
        }

        return typeCorps;
    }

    throw std::runtime_error("Expression inconnue");
}

// Crée un nom de variable temporaire.
std::string CompCode::nouveauTemp() {
    return "tmp" + std::to_string(cpt++);
}

// Compile une expression.
ResCode CompCode::comp(
    const ExprPtr& expr,
    Env env,
    const EnvFoncs& foncs,
    const EnvFoncsBin& foncsBin,
    const CtxPar& ctx
) {
    if (auto cst = std::dynamic_pointer_cast<CstEnt>(expr)) {
        std::string tmp = nouveauTemp();

        std::ostringstream sortie;
        sortie << "int " << tmp << " = " << cst->val << ";\n";

        return {sortie.str(), tmp, Type::Ent};
    }

    if (auto cst = std::dynamic_pointer_cast<CstFlot>(expr)) {
        std::string tmp = nouveauTemp();

        std::ostringstream sortie;
        sortie << "double " << tmp << " = " << cst->val << ";\n";

        return {sortie.str(), tmp, Type::Flot};
    }

    if (auto var = std::dynamic_pointer_cast<Var>(expr)) {
        return {"", var->nom, typeDe(expr, env, foncs, foncsBin)};
    }

    if (auto fonc = std::dynamic_pointer_cast<FoncUnaire>(expr)) {
        ResCode arg = comp(fonc->arg, env, foncs, foncsBin, ctx);
        Type typeRes = typeDe(expr, env, foncs, foncsBin);
        Type typeArg = typeDe(fonc->arg, env, foncs, foncsBin);
        auto sigOpt = trouverSigUnaire(fonc->nom, typeArg, foncs);
        if (!sigOpt.has_value()) {
            throw std::runtime_error("Mauvais type pour l'argument de " + fonc->nom);
        }
        std::string tmp = nouveauTemp();

        std::ostringstream sortie;
        sortie << arg.code;
        sortie << typeCpp(typeRes) << " " << tmp << " = "
            << nomFoncUnGen(fonc->nom) << "(" << arg.res << ")"
            << ";\n";

        return {sortie.str(), tmp, typeRes};
    }

    if (auto exprBin = std::dynamic_pointer_cast<ExprBin>(expr)) {
        ResCode gch = comp(exprBin->gch, env, foncs, foncsBin, ctx);
        ResCode drt = comp(exprBin->drt, env, foncs, foncsBin, ctx);
        Type typeRes = typeDe(expr, env, foncs, foncsBin);
        Type typeGch = typeDe(exprBin->gch, env, foncs, foncsBin);
        Type typeDrt = typeDe(exprBin->drt, env, foncs, foncsBin);
        std::string tmp = nouveauTemp();

        std::ostringstream sortie;
        sortie << gch.code;
        sortie << drt.code;

        if (exprBin->op == "+" || exprBin->op == "*" || exprBin->op == "-") {
            sortie << typeCpp(typeRes) << " " << tmp << " = "
                << "(" << gch.res << " " << exprBin->op << " " << drt.res << ");\n";
        } else if (exprBin->op == "/") {
            sortie << "double " << tmp << " = "
                << "(static_cast<double>(" << gch.res << ") / "
                << "static_cast<double>(" << drt.res << "));\n";
        } else {
            auto sigOpt = trouverSigBin(exprBin->op, typeGch, typeDrt, foncsBin);
            if (!sigOpt.has_value()) {
                throw std::runtime_error("Fonction binaire non définie : " + exprBin->op);
            }
            sortie << typeCpp(typeRes) << " " << tmp << " = "
                << nomFoncBinGen(exprBin->op) << "(" << gch.res << ", " << drt.res << ")"
                << ";\n";
        }

        return {sortie.str(), tmp, typeRes};
    }

    if (auto acces = std::dynamic_pointer_cast<AccesVecteur>(expr)) {
        ResCode vecteur = comp(acces->vecteur, env, foncs, foncsBin, ctx);
        ResCode indice = comp(acces->indice, env, foncs, foncsBin, ctx);
        Type typeRes = typeDe(expr, env, foncs, foncsBin);
        std::string tmp = nouveauTemp();

        std::ostringstream sortie;
        sortie << vecteur.code;
        sortie << indice.code;
        sortie << typeCpp(typeRes) << " " << tmp << " = genAccesVect("
            << vecteur.res << ", " << indice.res << ");\n";

        return {sortie.str(), tmp, typeRes};
    }

    if (auto somme = std::dynamic_pointer_cast<Somme>(expr)) {
        return compSomme(somme, env, foncs, foncsBin, ctx);
    }

    throw std::runtime_error("Expression inconnue");
}

// Compile une somme.
ResCode CompCode::compSomme(
    const std::shared_ptr<Somme>& somme,
    Env env,
    const EnvFoncs& foncs,
    const EnvFoncsBin& foncsBin,
    const CtxPar& ctx
) {
    ResCode bInf = comp(somme->bInf, env, foncs, foncsBin, ctx);
    ResCode bSup = comp(somme->bSup, env, foncs, foncsBin, ctx);

    if (bInf.type != Type::Ent || bSup.type != Type::Ent) {
        throw std::runtime_error("Les bornes d'une somme doivent être de type Int");
    }

    Env envLoc = env;
    envLoc[somme->ind] = Type::Ent;

    Type typeRes = typeDe(somme->corps, envLoc, foncs, foncsBin);
    if (estVecteur(typeRes)) {
        throw std::runtime_error("Une somme de vecteurs complets n'est pas encore supportee");
    }
    std::string acc = nouveauTemp();

    std::ostringstream sortie;
    sortie << bInf.code;
    sortie << bSup.code;

    if (somme->nat == NatSomme::Seq) {
        sortie << typeCpp(typeRes) << " " << acc << " = " << valNulle(typeRes) << ";\n";
        sortie << "for (int " << somme->ind << " = " << bInf.res
            << "; " << somme->ind << " <= " << bSup.res
            << "; ++" << somme->ind << ") {\n";

        ResCode corps = comp(somme->corps, envLoc, foncs, foncsBin, ctx);

        sortie << indenter(corps.code);
        sortie << "    " << acc << " += " << corps.res << ";\n";
        sortie << "}\n";

        return {sortie.str(), acc, typeRes};
    }

    if (!contientSommePar(somme->corps)) {
        std::string resGlob = nouveauTemp();

        // Cas parallèle simple.
        sortie << typeCpp(typeRes) << " " << acc << " = " << valNulle(typeRes) << ";\n";
        sortie << "if (" << ctx.actif << ") {\n";
        sortie << "    for (int " << somme->ind << " = " << bInf.res << " + " << ctx.rang
            << "; " << somme->ind << " <= " << bSup.res
            << "; " << somme->ind << " += " << ctx.nbProc << ") {\n";

        ResCode corps = comp(somme->corps, envLoc, foncs, foncsBin, ctx);

        sortie << indenter(indenter(corps.code));
        sortie << "        " << acc << " += " << corps.res << ";\n";
        sortie << "    }\n";
        sortie << "}\n";
        sortie << typeCpp(typeRes) << " " << resGlob << " = " << valNulle(typeRes) << ";\n";
        sortie << "MPI_Allreduce(&" << acc << ", &" << resGlob
            << ", 1, " << typeMpi(typeRes)
            << ", MPI_SUM, MPI_COMM_WORLD);\n";

        return {sortie.str(), resGlob, typeRes};
    }

    std::string nbGroupes = nouveauTemp();
    std::string tailleGroupe = nouveauTemp();
    std::string couleur = nouveauTemp();
    std::string rangEnfant = nouveauTemp();
    std::string tailleEnfant = nouveauTemp();
    std::string groupeResp = nouveauTemp();
    std::string resGlob = nouveauTemp();

    // Cas imbriqué.
    sortie << "int " << nbGroupes << " = (" << ctx.nbProc << " > 1) ? 2 : 1;\n";
    sortie << "int " << tailleGroupe << " = (" << ctx.nbProc << " + " << nbGroupes
        << " - 1) / " << nbGroupes << ";\n";
    sortie << "int " << couleur << " = " << ctx.rang << " / " << tailleGroupe << ";\n";
    sortie << "if (" << couleur << " >= " << nbGroupes << ") {\n";
    sortie << "    " << couleur << " = " << nbGroupes << " - 1;\n";
    sortie << "}\n";
    sortie << "int " << rangEnfant << " = " << ctx.rang << " - ("
        << couleur << " * " << tailleGroupe << ");\n";
    sortie << "int " << tailleEnfant << " = std::min(" << tailleGroupe
        << ", " << ctx.nbProc << " - (" << couleur << " * " << tailleGroupe << "));\n";
    sortie << typeCpp(typeRes) << " " << acc << " = " << valNulle(typeRes) << ";\n";
    sortie << "for (int " << somme->ind << " = " << bInf.res
        << "; " << somme->ind << " <= " << bSup.res
        << "; ++" << somme->ind << ") {\n";
    sortie << "    int " << groupeResp << " = ((" << somme->ind << " - " << bInf.res
        << ") % " << nbGroupes << " + " << nbGroupes << ") % " << nbGroupes << ";\n";

    CtxPar ctxEnfant{
        rangEnfant,
        tailleEnfant,
        "(" + ctx.actif + " && " + couleur + " == " + groupeResp + ")",
        ctx.niveau + 1
    };
    ResCode corps = comp(somme->corps, envLoc, foncs, foncsBin, ctxEnfant);

    sortie << indenter(corps.code);
    sortie << "    if (" << ctx.actif << " && " << couleur << " == " << groupeResp
        << " && " << rangEnfant << " == 0) {\n";
    sortie << "        " << acc << " += " << corps.res << ";\n";
    sortie << "    }\n";
    sortie << "}\n";
    sortie << typeCpp(typeRes) << " " << resGlob << " = " << valNulle(typeRes) << ";\n";
    sortie << "MPI_Allreduce(&" << acc << ", &" << resGlob
        << ", 1, " << typeMpi(typeRes)
        << ", MPI_SUM, MPI_COMM_WORLD);\n";

    return {sortie.str(), resGlob, typeRes};
}

// Indente un bloc de code.
std::string CompCode::indenter(const std::string& code) {
    std::ostringstream sortie;
    std::istringstream entree(code);
    std::string ligne;

    while (std::getline(entree, ligne)) {
        if (!ligne.empty()) {
            sortie << "    " << ligne << "\n";
        } else {
            sortie << "\n";
        }
    }

    return sortie.str();
}

// Génère le programme C++ complet.
std::string compilProg(const ExprPtr& expr, Env env, const EnvFoncs& foncs, const EnvFoncsBin& foncsBin) {
    CompCode compCode;
    CtxPar ctx{"rang", "nbProc", "true", 0};
    ResCode res = compCode.comp(expr, env, foncs, foncsBin, ctx);

    std::ostringstream sortie;

    sortie << "#include <algorithm>\n";
    sortie << "#include <cmath>\n";
    sortie << "#include <iomanip>\n";
    sortie << "#include <iostream>\n";
    sortie << "#include <numeric>\n";
    sortie << "#include <stdexcept>\n";
    sortie << "#include <string>\n";
    sortie << "#include <vector>\n\n";
    sortie << "#include <mpi.h>\n\n";

    sortie << "// Accède à un élément d'un vecteur.\n";
    sortie << "template <typename T>\n";
    sortie << "const T& genAccesVect(const std::vector<T>& valeurs, int indice) {\n";
    sortie << "    if (indice < 0 || static_cast<std::size_t>(indice) >= valeurs.size()) {\n";
    sortie << "        throw std::out_of_range(\"Indice vectoriel hors limites: \" + std::to_string(indice));\n";
    sortie << "    }\n";
    sortie << "    return valeurs[static_cast<std::size_t>(indice)];\n";
    sortie << "}\n\n";

    for (const auto& [nom, sigs] : foncs) {
        for (const auto& sig : sigs) {
            Type typeArg = sig.first;
            Type typeRes = sig.second;

            sortie << "// Définit une fonction unaire générée.\n";
            sortie << typeCpp(typeRes) << " " << nomFoncUnGen(nom)
                << "(" << typeCpp(typeArg) << " x) {\n";
            sortie << "    return " << corpsFoncUn(nom, typeArg, typeRes)
                << "; // corps a modifier\n";
            sortie << "}\n\n";
        }
    }

    for (const auto& [nom, sigs] : foncsBin) {
        for (const auto& sig : sigs) {
            Type typeArg1 = std::get<0>(sig);
            Type typeArg2 = std::get<1>(sig);
            Type typeRes = std::get<2>(sig);

            sortie << "// Définit une fonction binaire générée.\n";
            sortie << typeCpp(typeRes) << " " << nomFoncBinGen(nom)
                << "(" << typeCpp(typeArg1) << " x, " << typeCpp(typeArg2) << " y) {\n";
            sortie << "    return " << corpsFoncBin(nom, typeRes)
                << "; // corps a modifier\n";
            sortie << "}\n\n";
        }
    }

    sortie << "// Exécute le programme généré.\n";
    sortie << "int main(int nbArgs, char** arguments) {\n";
    sortie << "    MPI_Init(&nbArgs, &arguments);\n\n";

    sortie << "    int rang = 0;\n";
    sortie << "    int nbProc = 0;\n";
    sortie << "    MPI_Comm_rank(MPI_COMM_WORLD, &rang);\n";
    sortie << "    MPI_Comm_size(MPI_COMM_WORLD, &nbProc);\n\n";

    for (const auto& [nom, type] : env) {
        sortie << "    " << typeCpp(type) << " " << nom << " = " << valNulle(type)
            << "; // variable libre a modifier\n";
    }

    if (!env.empty()) {
        sortie << "\n";
    }

    sortie << CompCode::indenter(res.code);
    sortie << "\n";
    sortie << "    if (rang == 0) {\n";
    if (res.type == Type::Flot || res.type == Type::VectFlot) {
        sortie << "        std::cout << std::setprecision(17);\n";
    }
    if (estVecteur(res.type)) {
        sortie << "        std::cout << \"[\";\n";
        sortie << "        for (std::size_t i = 0; i < " << res.res << ".size(); ++i) {\n";
        sortie << "            if (i != 0) std::cout << \",\";\n";
        sortie << "            std::cout << " << res.res << "[i];\n";
        sortie << "        }\n";
        sortie << "        std::cout << \"]\" << std::endl;\n";
    } else {
        sortie << "        std::cout << " << res.res << " << std::endl;\n";
    }
    sortie << "    }\n\n";
    sortie << "    MPI_Finalize();\n";
    sortie << "    return 0;\n";
    sortie << "}\n";

    return sortie.str();
}

// Écrit le programme généré.
void ecrireProg(const std::string& chemin, const std::string& programme) {
    std::ofstream sortie(chemin);

    if (!sortie) {
        throw std::runtime_error("Impossible d'ouvrir : " + chemin);
    }

    sortie << programme;
}
