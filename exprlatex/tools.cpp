#include <string_view>
#include <iostream>
#include <fstream>
#include <sstream>
#include "Expr.h"



// Useful for string pattern-matching (inside "switch")
// Code from https://medium.com/@ryan_forrester_/using-switch-statements-with-strings-in-c-a-complete-guide-efa12f64a59d
constexpr uint64_t hash(std::string_view str) {
    uint64_t hash = 0;
    for (char c : str) {
        hash = (hash * 131) + c;
    }
    return hash;
}

constexpr uint64_t operator"" _hash(const char* str, size_t len) {
    return hash(std::string_view(str, len));
}


/* **************************************************** */
/* **************************************************** */
/* --------------- Expression manipulation ------------ */
/* **************************************************** */
/* **************************************************** */


/* **************************************************** */
/* ---------------- subtitution ----------------------- */
/* **************************************************** */
/**
 * @brief  Appliquer une substitution d'une valeur dans un node pour une variable donnée; les lieurs sont les sommes
 * @param ExprPts le noeud dans lequel on appliquera la substitution
 * @param var la variable substituée
 * @param value par quoi on substitue la variable
 * @return le node avec var substitué par value
 */
ExprPtr substitute(ExprPtr node, char var, ExprPtr value) {
    // *** Case INT ***
    if (auto intNode = dynamic_cast<IntNode*>(node.get())) {
        return std::make_shared<IntNode>(*intNode);
    }
    // *** Case DOUBLE ***
    else if (auto doubleNode = dynamic_cast<DoubleNode*>(node.get())) {
        return std::make_shared<DoubleNode>(*doubleNode);
    }
    // *** Case IDENT ***
    else if (auto identNode = dynamic_cast<IdentNode*>(node.get())) {
        if (identNode->value == var) {
            return value;
        } else {
            return std::make_shared<IdentNode>(*identNode);
        }
    }
    // *** Case BINARY OP ***
    else if (auto binaryOpNode = dynamic_cast<BinaryOpNode*>(node.get())) {
        return std::make_shared<BinaryOpNode>(
            binaryOpNode->op,
            substitute(binaryOpNode->left, var, value),
            substitute(binaryOpNode->right, var, value)
        );
    }
    // *** Case UNARY OP ***
    else if (auto unaryOpNode = dynamic_cast<UnaryOpNode*>(node.get())) {
        return std::make_shared<UnaryOpNode>(
            unaryOpNode->op,
            substitute(unaryOpNode->sub, var, value)
        );
    }
    // *** Case FUNCTION CALL ***
    else if (auto funCallNode = dynamic_cast<FunCallNode*>(node.get())) {
        std::vector<ExprPtr> newSub;
        for (const auto& sub : funCallNode->sub) {
            newSub.push_back(substitute(sub, var, value));
        }
        return std::make_shared<FunCallNode>(funCallNode->name, newSub);
    }
    // *** Case BIG SUM ***
    else if (auto bigSumNode = dynamic_cast<BigSumNode*>(node.get())) {
        return std::make_shared<BigSumNode>(
            bigSumNode->indice,
            substitute(bigSumNode->under, var, value),
            substitute(bigSumNode->over, var, value),
            (bigSumNode->indice == var) ? bigSumNode->sub : substitute(bigSumNode->sub, var, value)
        );
    }
    // *** Case unknown ***
    else {
        throw std::runtime_error("Unknown node type in substitute");
    }
}



/* **************************************************** */
/* --------------- FUNCTION To Operation -------------- */
/* **************************************************** */
/**
 * @brief  Transformer certaines fonction LaTeX en des opérateurs. Par exemple "\dfrac" en "\". Si la transformation est impossible alors on retourne le string " " (juste un espace)
 * @param nbArgs le nombre d'argument, si !=2 alors pas de transformation possible (actuellement)
 * @param name la fonction LaTeX a eventuellement transformer
 * @return " " is pas de transformation sinon l'opérateur correcpondant à la fonction  (actuellement, frac, dfrac, tfrac, cfrac sont traités)
 */
std::string fromFunctionToOperation(int nbArgs, std::string_view name) {
    if (nbArgs!=2)
        return " ";
    else
        switch (hash(name)) {
            case "\\frac"_hash: return "/";
            case "\\dfrac"_hash: return "/";
            case "\\tfrac"_hash: return "/";
            case "\\cfrac"_hash: return "/";
            default: return " ";
        }
}