#pragma once

#include "formexec_types.hpp"

#include <map>
#include <string>
#include <vector>

// Construit les cas à lancer pour une section FormExec.
std::vector<std::map<std::string, ValScalaire>> construireCas(const DonneesSection& donnees);
