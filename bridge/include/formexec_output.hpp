#pragma once

#include "formexec_types.hpp"

#include <filesystem>
#include <string>
#include <vector>

// Écrit un fichier .formSkel.out au format FormExec.
void ecrireSortie(
    const std::filesystem::path& cheminSortie,
    const std::vector<CasExec>& cas,
    const std::vector<int>& procs,
    bool estMulti
);

// Écrit un fichier d'erreur lisible par FormExec.
void ecrireErreur(const std::filesystem::path& cheminSortie, const std::string& message);
