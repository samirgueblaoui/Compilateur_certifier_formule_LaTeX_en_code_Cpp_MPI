#include "parse_exprlatex.hpp"

#include <fstream>
#include <stdexcept>
#include <vector>

#include "../exprlatex/Expr.h"
#include "../exprlatex/ExprLexer.h"
#include "../exprlatex/ExprParser.h"
#include "../exprlatex/VectorTokenSource.cpp"

namespace {

// Convertit un type de jeton en indice de matrice.
int typeJetonVersInd(int typeJeton) {
    switch (typeJeton) {
        case ExprLexer::INT:
        case ExprLexer::DOUBLE:
        case ExprLexer::DOUBLEExt: return 0;
        case ExprLexer::IDENT:     return 1;
        case ExprLexer::LEFTPAR:   return 2;
        case ExprLexer::RIGHTPAR:  return 3;
        case ExprLexer::BigSUM:    return 4;
        case ExprLexer::LEFTB:     return 5;
        case ExprLexer::RIGHTB:    return 6;
        case ExprLexer::FACT:      return 7;
        case ExprLexer::FUNCTION:  return 8;
        default: return -1;
    }
}

// Indique si deux jetons exigent une multiplication implicite.
bool doitAjouterMultImpl(antlr4::Token* gch, antlr4::Token* drt) {
    bool multImplValide[9][9] = {
     /* nombre */ {false, true,  true,  false, true,  false, false, false, false},
     /* var    */ {false, true,  true,  false, true,  false, false, false, false},
     /* (      */ {false, false, false, false, false, false, false, false, false},
     /* )      */ {true,  true,  true,  false, true,  false, false, false, true},
     /* somme  */ {false, false, false, false, false, false, false, false, false},
     /* {      */ {false, false, false, false, false, false, false, false, false},
     /* }      */ {false, false, false, false, true,  false, false, false, false},
     /* !      */ {false, false, false, false, true,  false, false, false, false},
     /* fonc   */ {false, false, false, false, false, false, false, false, false}
    };

    int indGch = typeJetonVersInd(gch->getType());
    int indDrt = typeJetonVersInd(drt->getType());

    if (indGch == -1 || indDrt == -1) {
        return false;
    }

    return multImplValide[indGch][indDrt];
}

// Construit le flux de jetons avec les multiplications implicites.
antlr4::CommonTokenStream construireFlux(antlr4::Lexer* analyseurLex) {
    std::vector<std::unique_ptr<antlr4::Token>> jetons;

    auto* fluxBrut = new antlr4::CommonTokenStream(analyseurLex);
    fluxBrut->fill();

    antlr4::Token* prec = nullptr;
    for (antlr4::Token* cour : fluxBrut->getTokens()) {
        if (prec != nullptr && doitAjouterMultImpl(prec, cour)) {
            auto* multImpl = new antlr4::CommonToken(ExprParser::IMUL, "*");
            jetons.push_back(std::unique_ptr<antlr4::Token>(multImpl));
        }

        jetons.push_back(std::unique_ptr<antlr4::Token>(cour));
        prec = cour;
    }

    return antlr4::CommonTokenStream(new VectorTokenSource(std::move(jetons)));
}

} // namespace

// Lit et analyse une expression LaTeX depuis un fichier.
std::shared_ptr<ExprNode> lireExprLatex(const std::string& cheminEntree) {
    std::ifstream ficEntree(cheminEntree);
    if (!ficEntree.is_open()) {
        throw std::runtime_error("Impossible d'ouvrir le fichier d'entree : " + cheminEntree);
    }

    antlr4::ANTLRInputStream entreeAntlr(ficEntree);
    ExprLexer analyseurLex(&entreeAntlr);
    antlr4::CommonTokenStream jetons = construireFlux(&analyseurLex);
    ExprParser analyseurSyn(&jetons);

    return analyseurSyn.start()->node;
}
