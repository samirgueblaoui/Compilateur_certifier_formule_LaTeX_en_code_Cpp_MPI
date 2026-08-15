#include "compilateur.hpp"
#include "compilateur_outils.hpp"

#include "convert_exprlatex_to_compilateur.hpp"
#include "parse_exprlatex.hpp"

#include <iostream>
#include <stdexcept>

namespace {

// Renvoie le nom lisible d'un type.
std::string nomType(Type type) {
    switch (type) {
        case Type::Ent: return "Int";
        case Type::Flot: return "Float";
        case Type::VectEnt: return "VectorInt";
        case Type::VectFlot: return "VectorFloat";
    }
    return "Inconnu";
}

} // namespace

// Lance la génération du programme C++.
int main(int nbArgs, char* arguments[]) {
    if (nbArgs < 2 || nbArgs > 3) {
        std::cerr << "Usage: " << arguments[0] << " <input_file> [output_cpp]" << std::endl;
        return 1;
    }

    try {
        const std::string cheminEntree = arguments[1];
        const std::string cheminSortie =
            (nbArgs == 3) ? arguments[2] : "compilateur/src/compile.cpp";

        std::shared_ptr<ExprNode> astLatex = lireExprLatex(cheminEntree);
        ExprPtr expr = convertirExpr(astLatex);

        Env env;
        compilateur_outils::infererEnv(expr, env);

        EnvFoncs foncs;
        EnvFoncsBin foncsBin;
        compilateur_outils::construireEnvFoncs(expr, foncs, foncsBin);

        Type type = typeDe(expr, env, foncs, foncsBin);
        std::string programme = compilProg(expr, env, foncs, foncsBin);
        ecrireProg(cheminSortie, programme);

        std::cout << "Pipeline execute : ExprLatex -> AST compilateur -> generation" << std::endl;
        std::cout << "Fichier source : " << cheminEntree << std::endl;
        std::cout << "Type infere : " << nomType(type) << std::endl;
        std::cout << "Code genere dans " << cheminSortie << std::endl;
    } catch (const std::exception& erreur) {
        std::cerr << "Erreur : " << erreur.what() << std::endl;
        return 1;
    }

    return 0;
}
