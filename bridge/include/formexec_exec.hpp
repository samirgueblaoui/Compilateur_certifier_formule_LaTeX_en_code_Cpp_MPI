#pragma once

#include "formexec_types.hpp"

#include <filesystem>

// Compile le C++ généré en exécutable MPI.
void compilerProgGenere(
    const std::filesystem::path& cheminCpp,
    const std::filesystem::path& cheminExe
);

// Exécute le programme MPI et mesure sa durée.
MesureExec executerProgGenere(const std::filesystem::path& cheminExe, int nbProc);
