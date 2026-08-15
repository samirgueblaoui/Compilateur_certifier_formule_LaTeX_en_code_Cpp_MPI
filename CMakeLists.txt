cmake_minimum_required(VERSION 3.16)

project(stgm2 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

set(LATEX_INPUT_FILE "${CMAKE_SOURCE_DIR}/exprlatex/input.tex" CACHE FILEPATH
    "Fichier LaTeX a parser")
set(GENERATED_CPP_FILE "${CMAKE_SOURCE_DIR}/compilateur/src/compile.cpp" CACHE FILEPATH
    "Fichier C++ genere par le compilateur")
set(RUN_MPI_PROCESSES "4" CACHE STRING
    "Nombre de processus pour la cible run_generated")

find_package(MPI REQUIRED)
find_package(nlohmann_json CONFIG REQUIRED
    HINTS /opt/homebrew/Cellar/nlohmann-json/3.12.0/share/cmake/nlohmann_json)

find_path(ANTLR4_INCLUDE_DIR
    NAMES antlr4-runtime.h
    HINTS
        /opt/homebrew/include/antlr4-runtime
        /usr/local/include/antlr4-runtime
        /usr/include/antlr4-runtime
)

find_library(ANTLR4_LIBRARY
    NAMES antlr4-runtime
    HINTS
        /opt/homebrew/lib
        /usr/local/lib
        /usr/lib
)

if(NOT ANTLR4_INCLUDE_DIR OR NOT ANTLR4_LIBRARY)
    message(FATAL_ERROR
        "Runtime ANTLR4 C++ introuvable. "
        "Installe antlr4-cpp-runtime puis relance CMake.")
endif()

add_executable(latex_compiler_driver
    exprlatex/tools.cpp
    exprlatex/ExprLexer.cpp
    exprlatex/ExprParser.cpp
    bridge/src/parse_exprlatex.cpp
    bridge/src/convert_exprlatex_to_compilateur.cpp
    bridge/src/choose_sum_strategy.cpp
    compilateur/src/compilateur.cpp
    compilateur/src/compilateur_outils.cpp
    compilateur/src/main.cpp
)

target_include_directories(latex_compiler_driver PRIVATE
    ${ANTLR4_INCLUDE_DIR}
    ${CMAKE_SOURCE_DIR}/exprlatex
    ${CMAKE_SOURCE_DIR}/bridge/include
    ${CMAKE_SOURCE_DIR}/compilateur/include
)

target_link_libraries(latex_compiler_driver PRIVATE ${ANTLR4_LIBRARY})

add_executable(formexec_bridge_driver
    exprlatex/tools.cpp
    exprlatex/ExprLexer.cpp
    exprlatex/ExprParser.cpp
    bridge/src/parse_exprlatex.cpp
    bridge/src/convert_exprlatex_to_compilateur.cpp
    bridge/src/choose_sum_strategy.cpp
    bridge/src/formexec_config.cpp
    bridge/src/formexec_cases.cpp
    bridge/src/formexec_pipeline.cpp
    bridge/src/formexec_exec.cpp
    bridge/src/formexec_output.cpp
    bridge/src/formexec_runner.cpp
    bridge/src/formexec_main.cpp
    compilateur/src/compilateur.cpp
    compilateur/src/compilateur_outils.cpp
)

target_include_directories(formexec_bridge_driver PRIVATE
    ${ANTLR4_INCLUDE_DIR}
    ${CMAKE_SOURCE_DIR}/exprlatex
    ${CMAKE_SOURCE_DIR}/bridge/include
    ${CMAKE_SOURCE_DIR}/compilateur/include
)

target_link_libraries(formexec_bridge_driver PRIVATE
    ${ANTLR4_LIBRARY}
    nlohmann_json::nlohmann_json
)

set_source_files_properties(${GENERATED_CPP_FILE} PROPERTIES GENERATED TRUE)

add_custom_command(
    OUTPUT ${GENERATED_CPP_FILE}
    COMMAND $<TARGET_FILE:latex_compiler_driver> ${LATEX_INPUT_FILE} ${GENERATED_CPP_FILE}
    DEPENDS
        latex_compiler_driver
        ${LATEX_INPUT_FILE}
        bridge/src/parse_exprlatex.cpp
        bridge/src/convert_exprlatex_to_compilateur.cpp
        bridge/src/choose_sum_strategy.cpp
        compilateur/src/compilateur.cpp
        compilateur/src/compilateur_outils.cpp
        compilateur/src/main.cpp
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    COMMENT "Generation de compilateur/src/compile.cpp a partir de ${LATEX_INPUT_FILE}"
    VERBATIM
)

add_custom_target(gen_code DEPENDS ${GENERATED_CPP_FILE})

add_executable(generated_mpi_program
    ${GENERATED_CPP_FILE}
)

add_dependencies(generated_mpi_program gen_code)
target_link_libraries(generated_mpi_program PRIVATE MPI::MPI_CXX)

if(MPIEXEC_EXECUTABLE)
    add_custom_target(run_generated
        COMMAND ${MPIEXEC_EXECUTABLE} ${MPIEXEC_NUMPROC_FLAG} ${RUN_MPI_PROCESSES}
                $<TARGET_FILE:generated_mpi_program>
        DEPENDS generated_mpi_program
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
        USES_TERMINAL
        COMMENT "Execution du programme MPI genere"
    )
endif()

message(STATUS "Fichier LaTeX utilise : ${LATEX_INPUT_FILE}")
message(STATUS "Fichier C++ genere    : ${GENERATED_CPP_FILE}")
