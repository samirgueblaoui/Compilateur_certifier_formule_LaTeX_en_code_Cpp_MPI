#pragma once

#include "compilateur.hpp"

#include <map>
#include <optional>

// Valeur connue utilisée pour spécialiser une expression.
struct ValConnue {
    Type type = Type::Flot;
    int valEnt = 0;
    double valFlot = 0.0;
};

// Environnement des valeurs connues.
using EnvValsConnues = std::map<std::string, ValConnue>;

// Options du modèle de coût utilisé pour choisir la stratégie d'une somme.
struct OptsStrSom {
    double coutFoncUnaireDef = 10.0; // Coût par défaut d'une fonction unaire.
    double coutFoncBinDef = 15.0; // Coût par défaut d'une fonction binaire complexe.
    double coutOpArith = 1.0; // Coût d'une opération arithmétique native.
    double coutAcc = 1.0; // Coût de la mise à jour de l'accumulateur.
    double coutCom = 8.0; // Paramètre g du modèle BSP.
    double coutSynchro = 20.0; // Paramètre l du modèle BSP.
    int nbProc = 4; // Nombre de processus supposé disponible.
    int minIterPar = 8; // Seuil minimal d'itérations pour le parallélisme.
    int tailleIntervDef = 32; // Taille utilisée quand l'intervalle est inconnu.
    int nbGrpImb = 2; // Nombre de groupes supposé pour une somme imbriquée.
    double volReduc = 1.0; // Volume d'une réduction parallèle.
    std::map<std::string, double> coutsFoncsUnaires; // Coûts des fonctions unaires.
    std::map<std::string, double> coutsFoncsBin; // Coûts des fonctions binaires.
};

// Évalue statiquement une expression entière.
std::optional<int> evalEntStat(const ExprPtr& expr);

// Estime le travail nécessaire pour une expression.
double estimeTravExpr(const ExprPtr& expr, const OptsStrSom& opts);

// Estime le coût séquentiel d'une somme.
double estimeCoutSomSeq(const std::shared_ptr<Somme>& somme, const OptsStrSom& opts);

// Estime le coût parallèle simple d'une somme.
double estimeCoutSomParSimple(const std::shared_ptr<Somme>& somme, const OptsStrSom& opts);

// Estime le coût parallèle imbriqué d'une somme.
double estimeCoutSomParImb(const std::shared_ptr<Somme>& somme, const OptsStrSom& opts);

// Estime le meilleur coût parallèle d'une somme.
double estimeCoutSomPar(const std::shared_ptr<Somme>& somme, const OptsStrSom& opts);

// Choisit la stratégie la moins coûteuse pour une somme.
NatSomme choisitStrSom(const std::shared_ptr<Somme>& somme, const OptsStrSom& opts = {});

// Spécialise une expression et recalcule la stratégie de ses sommes.
ExprPtr specialiserSommes(
    const ExprPtr& expr,
    const EnvValsConnues& vals,
    const OptsStrSom& opts = {}
);
