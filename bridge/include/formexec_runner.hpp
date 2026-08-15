#pragma once

#include "formexec_types.hpp"

#include <filesystem>

// Exécute un cas du pont FormExec.
int executerPont(const ConfigExec& config);

// Exécute tous les cas d'un dossier FormExec.
int executerDossier(
    const std::filesystem::path& dossierSkel,
    const std::filesystem::path& cheminConfig,
    const std::filesystem::path& dossierTrav
);
