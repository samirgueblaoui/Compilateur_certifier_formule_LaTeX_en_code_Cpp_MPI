#pragma once
#include <string_view>
#include "Expr.h"
#include <vector>


ExprPtr substitute(ExprPtr node, char var, ExprPtr value);

std::string fromFunctionToOperation(int nbArgs, std::string_view name);

/**
 * @brief Vérifie si un vecteur est vide ou contient des pointeurs nuls.
 * @tparam T Type des éléments du vecteur (doit être un pointeur).
 * @param vec Le vecteur à vérifier.
 * @return si le vecteur contient ou non un pointeur vide
 */
template<typename T>
bool validateVector(const std::vector<T>& vec) {
    static_assert(std::is_pointer<T>::value, "Ce template est conçu pour les vecteurs de pointeurs.");
    for (size_t i = 0; i < vec.size(); ++i)
        if (vec[i] == nullptr)
            return true;
    return false;
}
