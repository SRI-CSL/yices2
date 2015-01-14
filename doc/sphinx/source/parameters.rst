:tocdepth: 2

.. _search_parameters:

Search Parameters
=================

Several parameters control the heuristics used by the Yices SAT solver
and theory solvers. They can be set using function :c:func:`yices_set_param`.


SAT Solver Parameters
---------------------

Yices uses a CDCL SAT solver, similar to Minisat and Picosat. The following parameters
affect heuristics used by this SAT solver.


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

- Each learned clause has an activity score that decays
  geometrically.  After each conflict, the activity of all clauses
  not involved in this conflict is reduced by a factor equal to
  clause-decay (by default it's 0.999).  A smaller clause-decay
  causes clauses activity do go down faster.

- To trigger clause deletion: the solver uses a threshold = reduction-bound

  1) Initially the bound is set via:

     .. code-block:: none

	reduction-bound = max(r-threshold, r-fraction * number of clauses in initial problem)

  2) During the search:

     .. code-block:: none

	when the number of learned clauses >= reduction bound
        delete low-activity clauses
        reduction-bound  := r-factor * reduction-bound

     The deletion attempts to remove approximately half of the learned clauses.


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

The randomness parameter specifies how much random decisions are made during the search.
For example, if randomness is 0.1, approximately 10% of the decision variables are
picked randomly (and 90% of the decision variables are selected based on activity).

 

Once a decision variable 'x' is selected, the branching mode
determines whether 'x' is set to true or false.

  +----------------+-------------+----------------------------------------------+
  | Parameter	   | Value       |  Meaning                                     |
  | Name           |             |                                              |
  +================+=============+==============================================+
  | branching      | default     | Default branching (as in RSAT)               |
  |                +-------------+----------------------------------------------+
  |                | negative    | Always set 'x' to false                      |
  |                +-------------+----------------------------------------------+
  |                | positive    | Always set 'x' tor true                      |
  |                +-------------+----------------------------------------------+
  |                | theory      | Use default is 'x' is a pure Boolean,        |
  |                |             | delegate to the theory solver otherwise      |
  |                +-------------+----------------------------------------------+
  |                | th-neg      | Set 'x' to false if it's a pure Boolean,     |
  |                |             | delegate to the theory solver otherwise      |
  |                +-------------+----------------------------------------------+
  |                | th-pos      | Set 'x' to true if it's a pure Boolean,      |
  |                |             | delegate to the theory solver otherwise      |
  +----------------+-------------+----------------------------------------------+

The default branching heuristic is standard. It uses a cache to remember the last
value assigned to each Boolean variable (either true or false). When 'x' is picked
as decision variable, then it is assigned the cached value (i.e., the last value
assigned to 'x'). At the beginning of the search, 'x' may not have a value yet.
In this case, the decision is to set 'x' to  faslse.

Delegating to the theory solver, means asking the theory solver to
evaluate the atom attached to 'x' in the theory solver's current model
then branching accordingly. This is supported by the Egraph and by the
Simplex solver.  For example, if 'x' is attached to arithmetic atom
(<= n 4), then the Simplex solver examines the value of 'n' in its
current variable assignment.  If this value is more than 4, the decision
is 'x := false', otherwise, it's  'x := true'.




Theory Lemmas
-------------

Yices includes heuristics to build theory lemmas.  A theory lemma is a
clause that's true in a theory and get added to the clauses stored in
the SAT solver. The heuristics attempt to discover useful theory
lemmas and convert them into clauses. Three types of theory lemmas
are considered.

1) Generic lemmas: Theory solvers communicate with the CDCL SAT
   solver by generating so-called theory explanations. By default,
   these theory explanations are temporary. Optionally, Yices can
   convert these theory explanations into clauses (thus making them
   permanent).


2) Simplex lemmas: If the Simplex solver contains atoms (<= n 4) and
   (<= n 3) then a valid theory lemma is that (<= n 3) implies (<= n 4).

   So we can add the following clause:

       (or (not (<= n 3)) (<= n 4))


3) Ackermann Lemmas: If the Egraph contains terms (F x y) and
   (F x z) then we can add the following lemma

        y = z  implies (F x y) = (F x z)

   This is a known as Ackermann's lemma for the terms (F x y) and (F x z).

   Yices uses a variant of this lemmas for predicates. If the Egraph
   contains (P x) and (P y) where P is an uninterpreted predicate
   (i.e., (P x) and (P y) are Boolean), then the corresponding Ackermann
   lemma is written as two clauses:

        x = y and (P x) implies (P y)
        x = y and (P y) implies (P x)


   Generating Ackermann lemmas may require creating new equality atoms.
   For example in

        y = z implies (F x y) = (F x z):

   Yices may have to create as many as two atoms: the atom (y = z) and
   the atom ((F x y) = (F x z)).  Too many of these can overwhelm the
   Egraph. So Yices provides parameters to control the number of
   new equality atoms generated by the Ackermann lemmas heuristics.



The following parameters control lemma generation.


  +------------------------+-------------+----------------------------------------------+
  | Parameter	           | Type        |  Meaning                                     |
  | Name                   |             |                                              |
  +========================+=============+==============================================+
  | cache-tclauses         | Boolean     | enables the generation of                    |
  |                        |             | generic lemmas                               |
  +------------------------+-------------+----------------------------------------------+
  | tclause-size           | Integer     | bound on the size of generic lemmas          |
  +------------------------+-------------+----------------------------------------------+
  | dyn-ack	           | Boolean     | enables the generation of Ackermann lemmas   |
  |                        |             | for non-Boolean terms                        |
  +------------------------+-------------+----------------------------------------------+
  | max-ack	           | Integer     | bound on the number of Ackermann lemmas      |
  |                        |             | generated (for non-Boolean terms)            |
  +------------------------+-------------+----------------------------------------------+
  | dyn-ack-threshold      | Integer     | heuristic threshold: A lower value causes    |
  |                        |             | more lemmas to be generated                  |
  +------------------------+-------------+----------------------------------------------+
  | dyn-bool-ack           | Boolean     | enables the generation of Ackermann lemmas   |
  |                        |             | for Boolean terms                            |
  +------------------------+-------------+----------------------------------------------+
  | max-bool-ack           | Integer     | bound on the number of Boolean Ackermann     |
  |                        |             | lemmas generated                             |
  +------------------------+-------------+----------------------------------------------+
  | dyn-bool-ack-threshold | Integer     | heuristic threshold: as above. Lower values  |
  |                        |             | make lemma generation more aggressive        |
  +------------------------+-------------+----------------------------------------------+
  | aux-eq-quota	   | Integer     | limit on the number of equalities created    |
  |                        |             | for Ackermann lemmas                         |
  +------------------------+-------------+----------------------------------------------+
  | aux-eq-ratio           | Float       | another factor to limit the number of        |
  |                        |             | equalities created                           |
  +------------------------+-------------+----------------------------------------------+


If cache-tclauses is true, then only small theory explanations (that
contains no more than tclause-size literals) are converted to clauses.

To bound the number of new equality atoms created by the Ackermann and Boolean
Ackermann heuristics, Yices uses the two parameters aux-eq-quota and aux-eq-ratio.
The limit on the number of new equality atoms is set to

.. code-block:: none

    max(aux-eq-quota, num-terms * aux-eq-ratio)

where num-terms is the the total number of terms in the Egraph.




Simplex Parameters
------------------

The Simplex-base solver uses the following parameters


   eager-lemmas	      	   Boolean	   enable/disable the generation of lemmas in the Simplex
   			   		   solver. If this parameter is true, then the Simplex
					   solver will generate lemmas of the form

					   	  (x >= a) => (x >= b)

                                           where a and b are constants, and a > b.


   simplex-prop		   Boolean	   enable/disable theory propagation in the Simplex solver

   prop-threshold	   Integer	   bound on the number of variables in rows of the simplex
   			   		   tableau. If a row contains more than this number, it's
					   not considered during theory propagation.

   simplex-adjust	   Boolean 	   use a heuristic to adjust the simplex model

   bland-threhsold	   Integer	   number of pivoting steps before activation of Bland's
   			   		   pivoting rule

   icheck		   Boolean 	   enable periodic checking for integer feasibility
   			   		   If this flag is false, checking for integer feasibility
					   is done only at the end of the search.

   icheck-period           Integer	   if icheck is true, this parameter specifies how often the
   			   		   integer-feasibility check is called.



Array-solver Parameters
-----------------------

The array solver uses the following parameters.

    max-update-conflicts   Integer	   Bound on the number of 'update axioms' instantiated per
    			   		   call to the array solver's final

    max-extensionality	   Integer         Bound on the number of extensionality axioms instantiated
    			   		   per call to the arrays solver's final check.


Model Reconciliation Parameters
-------------------------------



     max-interface-eqs	   Integer	   Bound on the number of interface equalities created per
     			   		   call to the Egraph's final check.


Final check is called when the search completes. In this state,
all Boolean atoms are assigned a value and all solvers have a
local model that assigns values to variables managed by each
solver. A model-reconciliation procedure is then called to check
whether these local models are compatible: if two variables
x and y are shared between the Egraph and a theory solver, then
both the egraph and the solver must agree on whether x and y are
equal. If they are not, then Yices instantiates an interface
lemma for 'x' and 'y', to force agreement. Semantically, such a
lemmas encodes the rule

      'x == y' in the theory solver implies (eq x y) is true in the Egraph

For example, if x and y are shared between the Egraph and the Simplex solver,
Yices will generate the lemma

      ((eq x y) or (< x y) or (< y x))

where (eq x y) is an Equality atom in the Egraph and (< x y) and
(< y x) are arithmetic atoms in the Simplex solver.

max-interface-eqs is a bound on the number of such reconciliation lemmas.
At most max-interface-eqs lemmas are created for each call to the model
reconciliation procedure.
