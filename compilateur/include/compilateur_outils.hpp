#pragma once

#include "compilateur.hpp"

#include <optional>
#include <string>
#include <vector>

namespace compilateur_outils {

// Convertit un type vers son nom C++.
std::string typeCpp(Type type);

// Convertit un type vers son nom MPI.
std::string typeMpi(Type type);

// Renvoie la valeur nulle d'un type.
std::string valNulle(Type type);

// Renvoie le type commun de deux valeurs.
Type promouvoir(Type typeGch, Type typeDrt);

// Indique si un type est vectoriel.
bool estVecteur(Type type);

// Renvoie le type des éléments d'un vecteur.
Type typeElem(Type type);

// Indique si l'expression contient une somme parallèle.
bool contientSommePar(const ExprPtr& expr);

// Construit les environnements des fonctions utilisées.
void construireEnvFoncs(
    const ExprPtr& expr,
    EnvFoncs& foncs,
    EnvFoncsBin& foncsBin
);

// Infère les types des variables libres.
void infererEnv(const ExprPtr& expr, Env& env);

// Construit le nom C++ d'une fonction unaire.
std::string nomFoncUnGen(const std::string& nom);

// Construit le nom C++ d'une fonction binaire.
std::string nomFoncBinGen(const std::string& nom);

// Construit le corps d'une fonction unaire.
std::string corpsFoncUn(const std::string& nom, Type typeArg, Type typeRes);

// Construit le corps d'une fonction binaire.
std::string corpsFoncBin(const std::string& nom, Type typeRes);

// Indique si deux types sont compatibles.
bool typeCompat(Type obtenu, Type attendu);

// Cherche une signature binaire compatible.
std::optional<SigFoncBin> trouverSigBin(
    const std::string& nom,
    Type typeGch,
    Type typeDrt,
    const EnvFoncsBin& foncsBin
);

// Cherche une signature unaire compatible.
std::optional<SigFoncUnaire> trouverSigUnaire(
    const std::string& nom,
    Type typeArg,
    const EnvFoncs& foncs
);

} // namespace compilateur_outils
