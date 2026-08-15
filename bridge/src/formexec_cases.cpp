#include "formexec_cases.hpp"

// Construit les cas à lancer pour une section FormExec.
std::vector<std::map<std::string, ValScalaire>> construireCas(const DonneesSection& donnees) {
    std::vector<std::map<std::string, ValScalaire>> cas;
    if (donnees.varsMulti.empty()) {
        cas.push_back(donnees.varsFixes);
        return cas;
    }

    std::size_t nbCas = donnees.varsMulti.front().second.size();
    cas.resize(nbCas, donnees.varsFixes);
    for (std::size_t i = 0; i < nbCas; ++i) {
        for (const auto& [nom, vals] : donnees.varsMulti) {
            cas[i][nom] = vals[i];
        }
    }
    return cas;
}
