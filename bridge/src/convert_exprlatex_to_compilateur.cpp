#include "convert_exprlatex_to_compilateur.hpp"
#include "choose_sum_strategy.hpp"

#include <stdexcept>
#include <string>

#define ExprPtr ExprLatexExprPtr
#include "../exprlatex/Expr.h"
#undef ExprPtr

namespace {

// Convertit un identifiant caractère en chaîne.
std::string identVersChaine(char val) {
    return std::string(1, val);
}

// Convertit un nœud unaire ExprLatex.
ExprPtr convertirNoeudUnaire(const UnaryOpNode& noeud) {
    ExprPtr sousExpr = convertirExpr(noeud.sub);

    if (noeud.op == "-") {
        return std::make_shared<ExprBin>(
            "*",
            std::make_shared<CstEnt>(-1),
            sousExpr
        );
    }

    return std::make_shared<FoncUnaire>(noeud.op, sousExpr);
}

// Convertit un appel de fonction ExprLatex.
ExprPtr convertirAppelFonc(const FunCallNode& noeud) {
    if (noeud.sub.size() == 1) {
        return std::make_shared<FoncUnaire>(
            noeud.name,
            convertirExpr(noeud.sub.front())
        );
    }

    if (noeud.sub.size() == 2) {
        return std::make_shared<ExprBin>(
            noeud.name,
            convertirExpr(noeud.sub[0]),
            convertirExpr(noeud.sub[1])
        );
    }

    throw std::runtime_error(
        "Conversion impossible: seules les fonctions d'arite 1 ou 2 sont supportees"
    );
}

// Convertit un nœud de somme ExprLatex.
ExprPtr convertirNoeudSomme(const BigSumNode& noeud) {
    if (noeud.condition != nullptr) {
        throw std::runtime_error(
            "Conversion impossible: les sommes avec condition ne sont pas encore supportees"
        );
    }

    ExprPtr bInf = convertirExpr(noeud.under);
    ExprPtr bSup = convertirExpr(noeud.over);
    ExprPtr corps = convertirExpr(noeud.sub);

    auto somme = std::make_shared<Somme>(
        NatSomme::Seq,
        identVersChaine(noeud.indice),
        bInf,
        bSup,
        corps
    );

    somme->nat = choisitStrSom(somme);
    return somme;
}

} // namespace

// Convertit un nœud ExprLatex en expression du compilateur.
ExprPtr convertirExpr(const std::shared_ptr<ExprNode>& noeud) {
    if (!noeud) {
        throw std::runtime_error("Conversion impossible: noeud ExprLatex nul");
    }

    if (auto noeudEnt = std::dynamic_pointer_cast<IntNode>(noeud)) {
        return std::make_shared<CstEnt>(noeudEnt->value);
    }

    if (auto noeudFlot = std::dynamic_pointer_cast<DoubleNode>(noeud)) {
        return std::make_shared<CstFlot>(static_cast<double>(noeudFlot->value));
    }

    if (auto noeudIdent = std::dynamic_pointer_cast<IdentNode>(noeud)) {
        return std::make_shared<Var>(identVersChaine(noeudIdent->value));
    }

    if (auto noeudBin = std::dynamic_pointer_cast<BinaryOpNode>(noeud)) {
        if (noeudBin->op == "VectorAccess") {
            return std::make_shared<AccesVecteur>(
                convertirExpr(noeudBin->left),
                convertirExpr(noeudBin->right)
            );
        }

        return std::make_shared<ExprBin>(
            noeudBin->op,
            convertirExpr(noeudBin->left),
            convertirExpr(noeudBin->right)
        );
    }

    if (auto noeudUnaire = std::dynamic_pointer_cast<UnaryOpNode>(noeud)) {
        return convertirNoeudUnaire(*noeudUnaire);
    }

    if (auto noeudAppel = std::dynamic_pointer_cast<FunCallNode>(noeud)) {
        return convertirAppelFonc(*noeudAppel);
    }

    if (auto noeudSomme = std::dynamic_pointer_cast<BigSumNode>(noeud)) {
        return convertirNoeudSomme(*noeudSomme);
    }

    if (std::dynamic_pointer_cast<BoolNode>(noeud)) {
        throw std::runtime_error(
            "Conversion impossible: les booleens ExprLatex ne sont pas supportes par le compilateur"
        );
    }

    throw std::runtime_error("Conversion impossible: type de noeud ExprLatex inconnu");
}
