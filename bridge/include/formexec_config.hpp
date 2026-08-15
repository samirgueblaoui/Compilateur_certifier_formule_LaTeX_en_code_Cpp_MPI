#pragma once

#include "formexec_types.hpp"

#include <filesystem>

// Lit une section du JSON et en extrait les variables utiles au pipeline.
DonneesSection chargerSection(const std::filesystem::path& cheminConfig, int section);

// Matérialise à la demande un vecteur référencé par un fichier.
ValScalaire resoudreValFichier(const ValScalaire& val);
