#pragma once

#include "choose_sum_strategy.hpp"

#include "compilateur.hpp"

#include <filesystem>
#include <map>
#include <optional>
#include <string>
#include <vector>

// Valeur scalaire ou vectorielle prête à être injectée dans le programme généré.
struct ValScalaire {
    Type type = Type::Flot;
    std::string texte;
    // Les fichiers sont chargés seulement si la variable apparaît dans la formule.
    std::optional<std::filesystem::path> fichierSrc;
};

// Liaison entre une fonction LaTeX et son implémentation C++.
struct LiaisonFonc {
    std::string nomLatex;
    std::string nomCpp;
    int arite = 1;
    std::optional<double> coutNum;
    std::string coutBrut;
};

// Données numériques utiles à une section FormExec.
struct DonneesSection {
    std::map<std::string, ValScalaire> varsFixes;
    std::vector<int> procs{1};
    std::vector<std::pair<std::string, std::vector<ValScalaire>>> varsMulti;
    OptsStrSom optsSommes;
    std::vector<LiaisonFonc> liaisonsFoncs;
};

// Paramètres d'une exécution du pont FormExec vers le compilateur.
struct ConfigExec {
    std::filesystem::path cheminFormule;
    std::filesystem::path cheminSortie;
    std::filesystem::path cheminConfig;
    std::filesystem::path dossierTrav;
    int section = 1;
};

// Résultat d'une exécution pour un nombre de processus donné.
struct MesureExec {
    std::string val;
    long long dureeNs = 0;
};

// Ensemble des mesures d'un même cas SOLO ou MULTI.
struct CasExec {
    std::vector<MesureExec> mesures;
};
