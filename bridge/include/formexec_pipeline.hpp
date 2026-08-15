#pragma once

#include "formexec_types.hpp"

#include <filesystem>
#include <map>
#include <string>
#include <vector>

// Génère le programme C++ d'une formule.
std::filesystem::path genererProgramme(
    const std::filesystem::path& cheminFormule,
    const std::filesystem::path& cheminCpp,
    const std::map<std::string, ValScalaire>& valeurs,
    const OptsStrSom& optsSom
);

// Lit tout le contenu d'un fichier.
std::string lireFichier(const std::filesystem::path& chemin);

// Écrit tout le contenu d'un fichier.
void ecrireFichier(const std::filesystem::path& chemin, const std::string& contenu);

// Complète le code généré avec les valeurs et les fonctions configurées.
std::string completerCodeGenere(
    std::string code,
    const std::map<std::string, ValScalaire>& valeurs,
    const std::vector<LiaisonFonc>& liaisons
);
