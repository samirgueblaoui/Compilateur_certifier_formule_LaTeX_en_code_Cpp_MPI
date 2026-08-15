#pragma once

#include <memory>
#include <string>

class ExprNode;

// Lit et analyse une expression LaTeX depuis un fichier.
std::shared_ptr<ExprNode> lireExprLatex(const std::string& cheminEntree);
