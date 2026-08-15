/*
Pour installer ANTLR
    https://www.cs.sjsu.edu/~mak/tutorials/InstallANTLR4Cpp.pdf

Pour compiler
    java -jar ../antlr-4.13.2-complete.jar -no-listener -no-visitor -encoding UTF-8 -Dlanguage=Cpp Expr.g4

    java -jar ../antlr-4.13.2-complete.jar -no-listener -no-visitor -encoding UTF-8 -Dlanguage=Cpp ExprLexer.g4
    java -jar ../antlr-4.13.2-complete.jar -no-listener -no-visitor -encoding UTF-8 -Dlanguage=Cpp ExprParser.g4

    g++ -std=c++23 main.cpp Expr*.cpp -lantlr4-runtime -I /usr/local/include/antlr4-runtime -o parser

Pour exécuter
    ./parser ../input.txt 

Pour tester la syntax
    java -jar ../antlr-4.13.2-complete.jar -encoding UTF-8 org.antrl.v4.gui.TestRig Expr.g4 start -gui
*/

#include <iostream>
#include <fstream>
#include <sstream>
#include "ExprLexer.h"
#include "ExprParser.h"
#include "Expr.h"
#include "VectorTokenSource.cpp"


// ***************************************
// ---------- util : détection ----------
// ***************************************
// Ces fonctions sont utilisées pour détecter les endroits où nous devons injecter un token d'IMUL pour la multiplication implicite, par exemple entre un nombre et une variable, ou entre une variable et une parenthèse ouvrante.
/* bool isFactorEnd(Token* t) {
    int type = t->getType();
    return type == ExprLexer::INT       ||
           type == ExprLexer::DOUBLE    ||
           type == ExprLexer::DOUBLEExt ||
           type == ExprLexer::IDENT     ||
           type == ExprLexer::RIGHTSQ   || // '] '
           type == ExprLexer::RIGHTB    || // '} '
           type == ExprLexer::RIGHTPAR;    // ') '
}

bool isFactorStart(Token* t) {
    int type = t->getType();
    return type == ExprLexer::INT       ||
           type == ExprLexer::DOUBLE    ||
           type == ExprLexer::DOUBLEExt ||
           type == ExprLexer::IDENT     ||
           type == ExprLexer::BigSUM    || // For example, in \sum_{i=1}^{n} i, we want to treat the \sum as a factor that can be multiplied by the following term, so we want to insert an IMUL token between \sum and the following term if there is no operator in between.
           type == ExprLexer::LEFTSQ    || // '['            
           type == ExprLexer::LEFTB     || // '{'
           type == ExprLexer::LEFTPAR;     // '('
}
           */

int tokenTypeToIndex(int type) {
    switch (type) {
        case ExprLexer::INT:
        case ExprLexer::DOUBLE:
        case ExprLexer::DOUBLEExt: return 0;  // number
        case ExprLexer::IDENT:     return 1;  // var
        case ExprLexer::LEFTPAR:   return 2;  // (
        case ExprLexer::RIGHTPAR:  return 3;  // )
        case ExprLexer::BigSUM:    return 4;  // bigsum
        case ExprLexer::LEFTB:     return 5;  // {
        case ExprLexer::RIGHTB:    return 6;  // }
        case ExprLexer::FACT:      return 7;  // !
        case ExprLexer::FUNCTION:  return 8;  // FUNCTION
        default: return -1; // not a factor
    }
}

bool needsImplicitMul(Token* left, Token* right) {
    // TODO: \sum_{i=1}^{n} i, on a "} i" donc a priori besoin d'un IMUL entre } et i, mais dans le cas de x^{2*n} i alors ce serait plus oui...
    // TODO: Il faudrait un pré-traitement pour distinguer les } qui font partie d'une notation de somme ou de produit, et ceux qui font partie d'une parenthèse normale. Par exemple, dans \sum_{i=1}^{n} i, le } fait partie de la notation de somme, donc on ne veut pas insérer un IMUL entre } et i, alors que dans x^{2*n} i, le } fait partie d'une parenthèse normale, donc on veut insérer un IMUL entre } et i.
    // Il va y avoir aussi les {} qui ne sont pas interpreté par LaTeX
    // TODO: idem f(x) et x(y+1) sont confondus. Il faut donc trouver des parenthèses spéciales pour les fonctions, par exemple f\left(1,2\right) pour les différencier des parenthèses normales. Et on peut faire du pre-traitement des variables quand on sait qu'elles sont des fonctions et non de simples variables, pour les différencier dans le tableau de multiplication implicite.
   
    bool valideImplicitMul[9][9] = {
     //               0      1      2      3      4      5       6      7      8
     // left/right  Number  Var     (      )   bigsum    {       }      !    FUNCT
     /* number */  {false, true,  true,  false, true,  false, false, false, false},
     /* var    */  {false, true,  true,  false, true,  false, false, false, false},
     /* (      */  {false, false, false, false, false, false, false, false, false},
     /* )      */  {true,  true,  true,  false, true,  false, false, false, true},
     /* bigsum */  {false, false, false, false, false, false, false, false, false},
     /* {      */  {false, false, false, false, false, false, false, false, false},
     /* }      */  {false, false, false, false, true,  false, false, false, false},
     /* !      */  {false, false, false, false, true,  false, false, false, false},
     /* FUNCT  */  {false, false, false, false, false, false, false, false, false}
    };

    int indexLeft  = tokenTypeToIndex(left->getType());
    int indexRight = tokenTypeToIndex(right->getType());
    if (indexLeft == -1 || indexRight == -1) {
        return false; // If either token is not a factor, we don't need to insert an IMUL
    }
    return valideImplicitMul[indexLeft][indexRight];
}

// ***************************************
// ---------- token injection -----------
// ***************************************
antlr4::CommonTokenStream buildStream(Lexer* lexer) {

    std::vector<std::unique_ptr<antlr4::Token>> out;

    CommonTokenStream* raw = new CommonTokenStream(lexer);
    raw->fill();

    antlr4::Token* prev = nullptr;

    for (antlr4::Token* current : raw->getTokens()) {
        // ajout des multiplication implicites
        if (prev != nullptr && needsImplicitMul(prev, current)) {
            auto imul = new antlr4::CommonToken(ExprParser::IMUL, "*");
            out.push_back(std::unique_ptr<antlr4::Token>(imul));
        }
        // std::cout << current->getText() << std::endl;
        out.push_back(std::unique_ptr<antlr4::Token>(current));
        prev = current;
    }

    return CommonTokenStream(new VectorTokenSource(std::move(out)));   
}


// ***************************************
// ---------------- MAIN   ---------------
// ***************************************

int main(int argc, char* argv[]) {
    if (argc != 2) {
        std::cerr << "Usage: " << argv[0] << " <input_file>" << std::endl;
        return 1;
    }
    // Lire le fichier d'entrée
    std::ifstream inputFile(argv[1]);
    if (!inputFile.is_open()) {
        std::cerr << "Error: Could not open file " << argv[1] << std::endl;
        return 1;
    }
    // Initialiser ANTLR
    antlr4::ANTLRInputStream antlrInput(inputFile);
    ExprLexer lexer(&antlrInput);
    antlr4::CommonTokenStream tokens = buildStream(&lexer);
    ExprParser parser(&tokens);

    // Parser et construire l'AST
    ExprPtr ast = (parser.start())->node;

    // Afficher l'AST
    std::cout << "AST:" << std::endl;
    ast->print();

    return 0;
}




