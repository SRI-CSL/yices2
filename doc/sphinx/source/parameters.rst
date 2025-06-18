:tocdepth: 2

.. include:: macros

.. _heuristic_parameters:

Heuristic Parameters
====================

Several parameters control the heuristics used by the Yices SAT solver
and theory solvers. They can be set using function :c:func:`yices_set_param`.


SAT Solver Parameters
---------------------

Yices uses a CDCL SAT solver, similar to Minisat [ES2003]_ and Picosat
[Bie2008]_.  The following parameters affect heuristics used by this
SAT solver.


Restart Heuristics
..................

The following parameters control the restart strategy.

  +----------------+-------------+----------------------------------------------+
  | Parameter	   | Type        |  Meaning                                     |
  | Name           |             |                                              |
  +================+=============+==============================================+
  | fast-restart   | Boolean     | If true, Yices will use a fast restart       |
  |                |             | heuristics                                   |
  +----------------+-------------+----------------------------------------------+
  | c-threshold	   | Integer     | Number of conflict before the first restart  |
  +----------------+-------------+----------------------------------------------+
  | c-factor	   |  Float	 | Increase factor for c-threshold after every  |
  |                |             | restart (must be >= 1.0)                     |
  +----------------+-------------+----------------------------------------------+
  | d-threshold	   | Integer     | Secondary threshold used only if             |
  |                |             | fast-restart is true                         |
  +----------------+-------------+----------------------------------------------+
  | d-factor       | Float       | Increase factor for d-threshold              |
  |                |             | (must be >= 1.0)                             |
  +----------------+-------------+----------------------------------------------+


If fast-restart is false, the following procedure is used (restart with a geometric progression):

.. code-block:: none

    c := c-threshold
    while not solved
       cdcl search
       when number of conflicts == c
         restart the search
         c := c-factor * c

If fast-restart is true, the following procedure is used (Picosat-like restart):

.. code-block:: none

   d := d-threshold
   c := c-threshold
   while not solved
      cdcl search
      when number of conflicts == c
         restart the search
         c := c_factor * c
         if c >= d then
            c := c_threshold
            d := d_factor * d




Clause deletion
...............

The CDCL SAT solver periodically deletes learned clauses that are judged useless.
The deletion procedure uses the following parameter.


  +----------------+-------------+----------------------------------------------+
  | Parameter	   | Type        |  Meaning                                     |
  | Name           |             |                                              |
  +================+=============+==============================================+
  | r-threshold    | Integer     | Initial clause-reduction threshold           |
  +----------------+-------------+----------------------------------------------+
  | r-fraction     | Float       | Clause-reduction fraction                    |
  |                |             | (must be between 0.0 and 1.0)                |
  +----------------+-------------+----------------------------------------------+
  | r-factor       | Float       | Increase factor for the reduction threshold  |
  |                |             | (must be >= 1.0)                             |
  +----------------+-------------+----------------------------------------------+
  | clause-decay   | Float       | Clause activity decay                        |
  |                |             | (must be between 0.0 and 1.0)                |
  +----------------+-------------+----------------------------------------------+

To control clause deletion, Yices uses the same strategy as Minisat
and other SAT solvers.

- Each learned clause has an activity score that decays geometrically.
  After each conflict, the activity of all clauses not involved in
  this conflict is reduced by a factor equal to clause-decay (by
  default it's 0.999).  A smaller value accelerates the decay.

- To trigger clause deletion: the solver uses a reduction-bound

  1) Initially the bound is set as follows:

     .. code-block:: none

	reduction-bound = max(r-threshold, r-fraction * number of clauses in initial problem)

  2) During the search, the bound determines when clauses are deleted:

     .. code-block:: none

	when the number of learned clauses >= reduction bound
        delete low-activity clauses
        reduction-bound  := r-factor * reduction-bound

     The deletion removes approximately half of the learned clauses.


Decision heuristic
..................

When the SAT solver makes a decision, it picks an unassigned Boolean variable
of highest activity or it picks a variable randomly.  Once this decision
variable is picked, the solver assigns it to true or false depending
on the branching mode.


Two parameters affect the choice of unassigned variable:

  +----------------+-------------+----------------------------------------------+
  | Parameter	   | Type        |  Meaning                                     |
  | Name           |             |                                              |
  +================+=============+==============================================+
  | var-decay      | Float       | Variable activity decay factor               |
  |                |             | (must be between 0 and 1.0)                  |
  +----------------+-------------+----------------------------------------------+
  | randomness     | Float       | Fraction of random decisions in branching    |
  |                |             | (must be between 0 and 1.0)                  |
  +----------------+-------------+----------------------------------------------+

The var-decay controls how fast variable activities go down. A smaller number
makes variable activities decay faster.

The randomness parameter specifies how many random decisions are made during the search.
For example, if randomness is 0.1, approximately 10% of the decision variables are
picked randomly (and 90% of the decision variables are selected based on activity).

Once a decision variable *x* is selected, the branching mode
determines whether *x* is set to true or false.

  +----------------+-------------+----------------------------------------------+
  | Parameter	   | Value       |  Meaning                                     |
  | Name           |             |                                              |
  +================+=============+==============================================+
  | branching      | default     | Default branching (as in RSAT)               |
  |                +-------------+----------------------------------------------+
  |                | negative    | Always set *x* to false                      |
  |                +-------------+----------------------------------------------+
  |                | positive    | Always set *x* to true                       |
  |                +-------------+----------------------------------------------+
  |                | theory      | Use default is *x* is a pure Boolean,        |
  |                |             | delegate to the theory solver otherwise      |
  |                +-------------+----------------------------------------------+
  |                | th-neg      | Set *x* to false if it's a pure Boolean,     |
  |                |             | delegate to the theory solver otherwise      |
  |                +-------------+----------------------------------------------+
  |                | th-pos      | Set *x* to true if it's a pure Boolean,      |
  |                |             | delegate to the theory solver otherwise      |
  +----------------+-------------+----------------------------------------------+

The default branching heuristic is standard. It uses a cache to remember the last
value assigned to each Boolean variable (either true or false). When *x* is picked
as decision variable, then it is assigned the cached value (i.e., the last value
assigned to *x*). At the beginning of the search, *x* may not have had a value yet.
In this case, the decision is to set *x* to  false.

Delegating to the theory solver means asking the theory solver to
evaluate the atom attached to *x* in the current model then branching
accordingly. This is supported by the egraph and by the Simplex
solver.  For example, if *x* is attached to arithmetic atom (*n* |le|
*4*), then the Simplex solver examines the value of *n* in its current
variable assignment.  If this value is more than 4, then *x* is set to
*false*, otherwise, *x* is set to *true*.



Theory Lemmas
-------------

Yices includes heuristics to build theory lemmas.  A theory lemma is a
clause that's true in a theory and get added to the clauses stored in
the SAT solver. The heuristics attempt to discover useful theory
lemmas and convert them into clauses. Three types of theory lemmas
are considered.

1) **Generic lemmas:** Theory solvers communicate with the CDCL SAT
   solver by generating so-called theory explanations. By default,
   these theory explanations are temporary. Optionally, Yices can
   convert these theory explanations into clauses (thus making them
   permanent).


2) **Simplex lemmas:** If the Simplex solver contains atoms (*n* |le| *4*) and
   (*n* |le| *3*) then a valid theory lemma  is (*n* |le| *3*) |implies| (*n* |le| *4*),
   which can be added as a clause to the SAT solver. Such a lemma is generated
   when assertions are processed if option *eager-arith-lemma* is active. 
   See :c:func:`yices_context_enable_option`.


3) **Ackermann lemmas:** If the egraph contains terms *(F x y)* and
   *(F x z)* then we can add the following lemma

   .. container:: lemma

      *y* = *z*  |implies| *(F x y)* = *(F x z)*

   This is a known as Ackermann's lemma for the terms *(F x y)* and *(F x z)*.

   Yices uses a variant of this lemmas for predicates. If the egraph
   contains *(P x)* and *(P y)* where P is an uninterpreted predicate
   (i.e., *(P x)* and *(P y)* are Boolean), then the corresponding Ackermann
   lemma is written as two clauses:

   .. container:: lemma

      *x* = *y* |and| *(P x)* |implies| *(P y)*

      *x* = *y* |and| *(P y)* |implies| *(P x)*


   Generating Ackermann lemmas may require creating new equality atoms.
   For example, in the clause

   .. container:: lemma

        *y* = *z*  |implies| *(F x y)* = *(F x z)*,

   Yices may have to create two new atoms: the atom (*y* = *z*) and
   the atom (*(F x y)* = *(F x z)*).  Too many of these can overwhelm the
   egraph so Yices provides parameters to control the number of
   new equality atoms generated by Ackermann lemmas.


The following parameters control generic lemma and Ackermann lemma generation.


  +------------------------+-------------+----------------------------------------------+
  | Parameter	           | Type        |  Meaning                                     |
  | Name                   |             |                                              |
  +========================+=============+==============================================+
  | cache-tclauses         | Boolean     | Enables the generation of                    |
  |                        |             | generic lemmas                               |
  +------------------------+-------------+----------------------------------------------+
  | tclause-size           | Integer     | Bound on the size of generic lemmas          |
  +------------------------+-------------+----------------------------------------------+
  | dyn-ack	           | Boolean     | Enables the generation of Ackermann lemmas   |
  |                        |             | for non-Boolean terms                        |
  +------------------------+-------------+----------------------------------------------+
  | max-ack	           | Integer     | Bound on the number of Ackermann lemmas      |
  |                        |             | generated (for non-Boolean terms)            |
  +------------------------+-------------+----------------------------------------------+
  | dyn-ack-threshold      | Integer     | Heuristic threshold: A lower value causes    |
  |                        |             | more lemmas to be generated                  |
  +------------------------+-------------+----------------------------------------------+
  | dyn-bool-ack           | Boolean     | Enables the generation of Ackermann lemmas   |
  |                        |             | for Boolean terms                            |
  +------------------------+-------------+----------------------------------------------+
  | max-bool-ack           | Integer     | Bound on the number of Boolean Ackermann     |
  |                        |             | lemmas generated                             |
  +------------------------+-------------+----------------------------------------------+
  | dyn-bool-ack-threshold | Integer     | Heuristic threshold: as above. Lower values  |
  |                        |             | make lemma generation more aggressive        |
  +------------------------+-------------+----------------------------------------------+
  | aux-eq-quota	   | Integer     | Limit on the number of equalities created    |
  |                        |             | for Ackermann lemmas                         |
  +------------------------+-------------+----------------------------------------------+
  | aux-eq-ratio           | Float       | Another factor to limit the number of        |
  |                        |             | equalities created                           |
  +------------------------+-------------+----------------------------------------------+


If cache-tclauses is true, then only small theory explanations (that
contains no more than tclause-size literals) are converted to clauses.

To bound the number of new equality atoms created by the Ackermann and Boolean
Ackermann heuristics, Yices uses the two parameters aux-eq-quota and aux-eq-ratio.
The limit on the number of new equality atoms is set to

.. code-block:: none

    max(aux-eq-quota, num-terms * aux-eq-ratio)

where num-terms is the the total number of terms initially present in
the egraph. When this limit is reached, Ackermann lemmas will not be
added if they require creating new equality atoms.




Simplex Parameters
------------------

The Simplex-based solver uses the following parameters.

  +------------------------+-------------+----------------------------------------------+
  | Parameter	           | Type        |  Meaning                                     |
  | Name                   |             |                                              |
  +========================+=============+==============================================+
  | simplex-prop           | Boolean	 |  Enables theory propagation in the Simplex   |
  |                        |             |  solver                                      |
  +------------------------+-------------+----------------------------------------------+
  | prop-threshold         | Integer     | Bound on the number of variables in rows     |
  |                        |             | of the simplex tableau: if a row contains    |
  |                        |             | more than this number of variables, it's     |
  |                        |             | not considered during theory propagation.    |
  +------------------------+-------------+----------------------------------------------+
  | simplex-adjust         | Boolean 	 | Uses a heuristic to adjust the simplex model |
  +------------------------+-------------+----------------------------------------------+
  | bland-threhsold        | Integer     | Number of pivoting steps before activation   |
  |                        |             | of Bland's pivoting rule                     |
  +------------------------+-------------+----------------------------------------------+
  | icheck                 | Boolean     | Enables periodic checking for integer        |
  |                        |             | feasibility If this flag is false, checking  |
  |                        |             | for integer feasibility is done only at the  |
  |                        |             | end of the search.                           |
  +------------------------+-------------+----------------------------------------------+
  | icheck-period          | Integer     | If icheck is true, this parameter specifies  |
  |                        |             | how often the integer-feasibility check is   |
  |                        |             | called.                                      |
  +------------------------+-------------+----------------------------------------------+



Array-solver Parameters
-----------------------

The array solver uses the following parameters.

  +------------------------+-------------+----------------------------------------------+
  | Parameter	           | Type        |  Meaning                                     |
  | Name                   |             |                                              |
  +========================+=============+==============================================+
  | max-update-conflicts   | Integer     | Bound on the number of 'update axioms'       |
  |                        |             | instantiated per call to the array solver's  |
  |                        |             | final check                                  |
  +------------------------+-------------+----------------------------------------------+
  | max-extensionality	   | Integer     | Bound on the number of extensionality axioms |
  |                        |             | instantiated per call to the arrays solver's |
  |                        |             | final check.                                 |
  +------------------------+-------------+----------------------------------------------+



Model Reconciliation Parameters
-------------------------------

Final check is called when the search completes. In this state,
all Boolean atoms are assigned a value and all solvers have a
local model that assigns values to variables managed by each
solver. A model-reconciliation procedure is then called to check
whether these local models are compatible: if two variables
*x* and *y* are shared between the egraph and a theory solver, then
both the egraph and the solver must agree on whether *x* and *y* are
equal.

If they are not, then Yices instantiate an interface lemma for *x* and
*y*, to force agreement. Semantically, such a lemmas encodes the rule

.. container:: lemma

   *x = y* in the theory solver implies *x = y*  in the egraph.

For example, if *x* and *y* are shared between the egraph and the Simplex solver,
then the interface lemma for *x* and *y* is

.. container:: lemma

   (*x* =  *y*) |or| (*x* < *y*) |or| (*y* < *x*)

where (*x* = *y*) is an equality atom in the egraph and (*x* < *y*) and
(*y* < *x*) are arithmetic atoms in the Simplex solver.

Optionally, before generating any interface lemma, Yices can attempt
to modify the egraph to locally solve the conflicts. This procedure is
explained in [Dut2014]_. We call it the *optimistic*
model-reconciliation procedure.


Model reconciliation is controlled by two parameters.

  +------------------------+-------------+----------------------------------------------+
  | Parameter	           | Type        |  Meaning                                     |
  | Name                   |             |                                              |
  +========================+=============+==============================================+
  | optimistic-final-check | Boolean     | Enable the optimistic model-reconciliation   |
  |                        |             | procedure                                    |
  +------------------------+-------------+----------------------------------------------+
  | max-interface-eqs	   | Integer     | Bound on the number of interface lemmas      |
  |                        |             | in each call to final check                  |
  +------------------------+-------------+----------------------------------------------+


Parameters Used by the Exists/Forall Solver
-------------------------------------------

Yices includes a solver for exists/forall problems, that is, problems of the form

.. container:: lemma

   |exists| x\ |_1| |...| x\ |_n| |forall| y\ |_1| |...| y\ |_m| P(x\ |_1| |...| x\ |_n|, y\ |_1| |...| y\ |_m|)


The algorithm used by Yices is explained in [Dut2015]_. It repeatedly
attempts to guess values for the existential variables x\ |_1| |...|
x\ |_n|, then checks whether these guesses are correct, by searching for
a counterexample in the variables y\ |_1| |...| y\ |_m|.

The following parameters control this algorithm.

  +------------------------+-------------+-------------------------------------------------+
  | Parameter	           | Type        |  Meaning                                        |
  | Name                   |             |                                                 |
  +========================+=============+=================================================+
  | ef-max-iters           | Integer     | Maximal number of iterations (this is a bound   |
  |                        |             | on the number of guesses before Yices gives up) |
  +------------------------+-------------+-------------------------------------------------+
  | ef-gen-mode            | Enum        | Selects the model-based generalization method   |
  |                        |             | (see below).                                    |
  +------------------------+-------------+-------------------------------------------------+
  | ef-max-samples         | Integer     | Limit on the number of samples used in the      |
  |                        |             | exists/forall solver's initialization           |
  +------------------------+-------------+-------------------------------------------------+
  | ef-flatten-iff         | Boolean     | Preprocessing option                            |
  +------------------------+-------------+-------------------------------------------------+
  | ef-flatten-ite         | Boolean     | Preprocessing option                            |
  +------------------------+-------------+-------------------------------------------------+

The generalization mode can take one of the following values:

  - none: no generalization is used

  - substitution: generalization by substitution

  - projection: model-based projection

  - auto: automatic. This is either generalization by substitution or model-based projection
    depending on the type of the universal variables.

The default setting is 'auto'. In this mode, Yices uses model-based projection if the
problems has arithmetic variables (i.e., integer or real-valued). Otherwise, it uses
generalization by substitution. See [Dut2015]_ and the references therein for more
details on model generalization.

Parameter ef-max-samples is used in the algorithm's initialization. In
this phase, Yices heuristically learns initial constraints on the existential
variables *x*. This is done by sampling values of the universal
variables *y*. The parameter is a bound on the number of these
samples.


The parameters ef-flatten-iff and ef-flatten-ite enable or disable
flattening of if-and-only-if and if-then-else terms, respectively.

Flattening *(<=> p q)* rewrites the term to *(and (=> p q) (=> q p))*

Flattening *(ite c p q)* rewrites the term to *(and (=> c p) (=> (not c) q)*

