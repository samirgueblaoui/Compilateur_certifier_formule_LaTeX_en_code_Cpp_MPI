#pragma once

#include <memory>

#include "compilateur.hpp"

class ExprNode;

// Convertit un nœud ExprLatex en expression du compilateur.
ExprPtr convertirExpr(const std::shared_ptr<ExprNode>& noeud);
