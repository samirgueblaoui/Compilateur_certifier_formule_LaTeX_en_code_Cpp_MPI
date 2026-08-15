#include "formexec_runner.hpp"

#include <filesystem>
#include <iostream>
#include <string>

// Lance le pont FormExec en mode fichier ou dossier.
int main(int nbArgs, char* arguments[]) {
    if (nbArgs == 2 || nbArgs == 3 || nbArgs == 4) {
        const std::filesystem::path dossierSkel = arguments[1];
        const std::filesystem::path cheminConfig =
            (nbArgs >= 3) ? arguments[2] : "FormExec/config.json";
        const std::filesystem::path dossierTrav =
            (nbArgs >= 4) ? arguments[3] : std::filesystem::path("build/formexec_runs");
        return executerDossier(dossierSkel, cheminConfig, dossierTrav);
    }

    if (nbArgs < 4 || nbArgs > 6) {
        std::cerr
            << "Usage: " << arguments[0]
            << " <formula_in> <section> <output_out> [config_json] [work_dir]\n"
            << "   ou: " << arguments[0]
            << " <formSkel_dir> [config_json] [work_dir]\n";
        return 1;
    }

    ConfigExec config;
    config.cheminFormule = arguments[1];
    config.section = std::stoi(arguments[2]);
    config.cheminSortie = arguments[3];
    config.cheminConfig = (nbArgs >= 5) ? arguments[4] : "FormExec/config.json";
    config.dossierTrav =
        (nbArgs >= 6) ? arguments[5] : std::filesystem::path("build/formexec_runs");

    return executerPont(config);
}
