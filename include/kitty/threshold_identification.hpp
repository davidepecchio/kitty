/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once


#include <vector>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"
#include <fstream>
#include "operations.hpp"
#include "static_truth_table.hpp"
#include "dynamic_truth_table.hpp"
#include "bit_operations.hpp"

enum Constraint_Type {
  G, L, E /* >=, <=, == */
};

struct Constraint {
  std::vector<uint64_t> variables;
  std::vector<int64_t> coefficients;
  Constraint_Type type;
  int constant; /* the right-hand side constant */
};

namespace kitty
{

/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt_fstar The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( TT& tt, std::vector<int64_t>* plf = nullptr )
{
  std::vector<int64_t> linear_form; //output vector
  
  bool greater = false;
  bool smaller = false;
  bool neg_unate = false;
  std::vector<bool> neg_unate_variables;

  uint64_t n_vars = tt.num_vars();
  uint64_t n_bits = tt.num_bits();

  for(uint64_t v = 0u; v < n_vars; v++) { //verify if negative unate or binate respect to variable v
    auto const cofact0 = cofactor0(tt, v);
    auto const cofact1 = cofactor1(tt, v);
    greater = false;
    smaller = false;

    for(uint64_t b = 0u; b < n_bits; b++) {
        if (get_bit(cofact1, b) > get_bit(cofact0, b)) {
            greater = true;
      }
        if (get_bit(cofact1, b) < get_bit(cofact0, b)) {
            smaller = true;
      }
    }

    if (greater == false && smaller == true) { //negative unate
        neg_unate = true;

      std::vector<bool> checked;
      for(uint64_t b = 0u; b < n_bits; b++) {
        checked.emplace_back(false);
      }

      for(uint64_t b = 0u; b < n_bits; b++) { //transform function f into function f* if negative unate
        if (checked[b] == false) {
          auto prev = get_bit(tt, b);
          auto next = get_bit(tt, b + (1u << v));
          if (prev == 1) {
              set_bit(tt, b + (1u << v));
          }
          if (prev == 0) {
              clear_bit(tt, b + (1u << v));
          }
          if (next == 1) {
              set_bit(tt, b);
          }
          if (next == 0) {
              clear_bit(tt, b);
          }
          checked[b] = true;
          checked[b + (1u << v)] = true;
        }
      }
    }
    neg_unate_variables.emplace_back(neg_unate);

    if (greater == true && smaller == true) { //binate
        return false;
    }
  }

  std::vector<Constraint> constraints; //constraints vector

  for(uint64_t b = 0; b < n_bits; b++) {
    Constraint constraint;
    for (uint64_t v = 0; v < n_vars; v++) {
        constraint.variables.emplace_back(v);
    }
    if (get_bit(tt, b) == 1) { 
        constraint.type = G;
        constraint.constant = 0;
    }
    if (get_bit(tt, b) == 0) {
        constraint.type = L;
        constraint.constant = -1.0;
    }
    constraint.variables.emplace_back(n_vars);
    constraints.emplace_back(constraint);
  }

  for(uint64_t v = 0; v < n_vars; v++) {
    uint8_t  c = 0;
    uint64_t b = 0;
    uint64_t pow = 1u << v;
    while(b < n_bits) {
      for (uint32_t p = 0; p < pow; p++ ) {
        constraints[b].coefficients.emplace_back(c);
        b++;
      }
      if (c == 0)
        c = 1;
      else
        c = 0;
    }
  }

  for(uint64_t b = 0; b < n_bits; b++) {
    constraints[b].coefficients.emplace_back(-1);
  }

  for(uint64_t v = 0; v <= n_vars; v++) {
    Constraint constraint;
    for(uint64_t i = 0; i <= n_vars; i++) {
      constraint.coefficients.emplace_back(0);
    }
    constraint.variables.emplace_back(v);
    constraint.coefficients[v] = 1;
    constraint.type = G;
    constraint.constant = 0;
    constraints.emplace_back(constraint);
  }

  /*LP solver*/

  lprec *lp;
  auto n_rows = constraints.size();
  std::vector<double> row;

  lp = make_lp(0, n_vars + 1);
  if(lp == nullptr) {
    return(false);
  }

  set_add_rowmode(lp, TRUE);

  row.emplace_back(1.0);
  for(uint64_t c = 1; c <= n_vars + 1; c++) {
    row.emplace_back(1.0);
  }
  set_obj_fn(lp, row.data());

  for(uint64_t r = 0; r < n_rows; r++) {
    for(uint64_t c = 1; c <= n_vars + 1; c++) {
      row[c] = constraints[r].coefficients[c-1];
    }
    if (constraints[r].type == G) {
        add_constraint(lp, row.data(), GE, constraints[r].constant);
    }
    if (constraints[r].type == L) {
        add_constraint(lp, row.data(), LE, constraints[r].constant);
    }
  }

  set_add_rowmode(lp, FALSE);
  set_minim(lp);

  for(auto v = 1u; v < n_vars + 1; v++) {
    set_int(lp, v, TRUE);
  }

  int result = solve(lp);
  if(result == OPTIMAL) {
    get_variables(lp, row.data());
    for(uint64_t v = 0; v < n_vars + 1; v++) {
      linear_form.push_back((int)(row[v]));
    }
  }
  else
    return false;

  if ( plf ) {
    *plf = linear_form;
  }
  return true;
}


} /* namespace kitty */
