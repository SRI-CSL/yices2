:tocdepth: 2

.. _smt_logics:

SMT Logics
==========

The following table lists the names of all the official SMT-LIB logics
at http://smt-lib.org (as of January 2015) and indicates whether Yices
supports them.  Currently, Yices supports most quantifier-free SMT-LIB
logics. Nonlinear real arithmetic is supported by using the MCSAT
solver of Yices.


   +------------+----------------------------------------------+------------+
   | Logic name | Description                                  | Supported  |
   +============+==============================================+============+
   | ALIA       | Arrays, Linear Integer                       | No         |
   |            | Arithmetic, Quantifiers                      |            |
   +------------+----------------------------------------------+------------+
   | AUFLIA     | Arrays, Uninterpreted Functions,             | No         |
   |            | Linear Integer Arithmetic, Quantifiers       |            |
   +------------+----------------------------------------------+------------+
   | AUFLIRA    | Arrays, Uninterpreted Functions,             | No         |
   |            | Mixed Linear Arithmetic, Quantifiers         |            |
   +------------+----------------------------------------------+------------+
   | AUFNIRA    | Arrays, Uninterpreted Functions,             | No         |
   |            | Mixed Nonlinear Arithmetic, Quantifiers      |            |
   +------------+----------------------------------------------+------------+
   | LIA        | Linear Integer Arithmetic, Quantifiers       | No         |
   |            |                                              |            |
   +------------+----------------------------------------------+------------+
   | LRA        | Linear Real Arithmetic, Quantifiers          | No         |
   |            |                                              |            |
   +------------+----------------------------------------------+------------+
   | NIA        | Nonlinear Integer Arithmetic, Quantifiers    | No         |
   |            |                                              |            |
   +------------+----------------------------------------------+------------+
   | NRA        | Nonlinear Real Arithmetic, Quantifiers       | No         |
   |            |                                              |            |
   +------------+----------------------------------------------+------------+
   | QF_ABV     | Arrays and Bitvectors                        | Yes        |
   |            |                                              |            |
   +------------+----------------------------------------------+------------+
   | QF_ALIA    | Arrays and Linear Integer Arithmetic         | Yes        |
   |            |                                              |            |
   +------------+----------------------------------------------+------------+
   | QF_AUFBV   | Arrays, Uninterpreted Functions, and         | Yes        |
   |            | Bitvectors                                   |            |
   +------------+----------------------------------------------+------------+
   | QF_AUFLIA  | Arrays, Uninterpreted Functions, and         | Yes        |
   |            | Linear Integer Arithmetic                    |            |
   +------------+----------------------------------------------+------------+
   | QF_AX      | Arrays (with extensionality)                 | Yes        |
   |            |                                              |            |
   +------------+----------------------------------------------+------------+
   | QF_BV      | Bitvectors                                   | Yes        |
   |            |                                              |            |
   +------------+----------------------------------------------+------------+
   | QF_IDL     | Integer Difference Logic                     | Yes        |
   |            |                                              |            |
   +------------+----------------------------------------------+------------+
   | QF_LIA     | Linear Integer Arithmetic                    | Yes        |
   |            |                                              |            |
   +------------+----------------------------------------------+------------+
   | QF_LRA     | Linear Real Arithmetic                       | Yes        |
   |            |                                              |            |
   +------------+----------------------------------------------+------------+
   | QF_NIA     | Nonlinear Integer Arithmetic                 | Yes        |
   |            |                                              |            |
   +------------+----------------------------------------------+------------+
   | QF_NIRA    | Mixed Nonlinear Arithmetic                   | Yes        |
   |            |                                              |            |
   +------------+----------------------------------------------+------------+
   | QF_NRA     | Nonlinear Real Arithmetic                    | Yes        |
   |            |                                              |            |
   +------------+----------------------------------------------+------------+
   | QF_RDL     | Real Difference Logic                        | Yes        |
   |            |                                              |            |
   +------------+----------------------------------------------+------------+
   | QF_UF      | Uninterpreted Functions                      | Yes        |
   |            |                                              |            |
   +------------+----------------------------------------------+------------+
   | QF_UFBV    | Uninterpreted Functions and                  | Yes        |
   |            | Bitvectors                                   |            |
   +------------+----------------------------------------------+------------+
   | QF_UFIDL   | Uninterpreted Functions and                  | Yes        |
   |            | Integer Difference Logic                     |            |
   +------------+----------------------------------------------+------------+
   | QF_UFLIA   | Uninterpreted Functions and                  | Yes        |
   |            | Linear Integer Arithmetic                    |            |
   +------------+----------------------------------------------+------------+
   | QF_UFLRA   | Uninterpreted Functions and                  | Yes        |
   |            | Linear Real Arithmetic                       |            |
   +------------+----------------------------------------------+------------+
   | QF_UFNIA   | Uninterpreted Functions and                  | Yes        |
   |            | Nonlinear Integer Arithmetic                 |            |
   +------------+----------------------------------------------+------------+
   | QF_UFNIRA  | Uninterpreted Functions and                  | Yes        |
   |            | Mixed Nonlinear Arithmetic                   |            |
   +------------+----------------------------------------------+------------+
   | QF_UFNRA   | Uninterpreted Functions and                  | Yes        |
   |            | Nonlinear Real Arithmetic                    |            |
   +------------+----------------------------------------------+------------+
   | UFLRA      | Uninterpreted Functions,                     | No         |
   |            | Linear Real Arithmetic, Quantifiers          |            |
   +------------+----------------------------------------------+------------+
   | UFNIA      | Uninterpreted Functions,                     | No         |
   |            | Nonlinear Integer Arithmetic, Quantifiers    |            |
   +------------+----------------------------------------------+------------+
   

Yices also recognizes and supports some logic names that are not
officially part of SMT-LIB.

   +------------+----------------------------------------------+
   | Logic name | Description                                  |
   +============+==============================================+
   | QF_ALRA    | Arrays and Linear Real Arithmetic            |
   |            |                                              |
   +------------+----------------------------------------------+
   | QF_ALIRA   | Arrays and Mixed Linear Arithmetic           |
   |            |                                              |
   +------------+----------------------------------------------+
   | QF_AUF     | Arrays and Uninterpreted Functions           |
   |            |                                              |
   +------------+----------------------------------------------+
   | QF_AUFLRA  | Arrays, Uninterpreted Functions,             |
   |            | Linear Real Arithmetic                       |
   +------------+----------------------------------------------+
   | QF_AUFLIRA | Arrays, Uninterpreted Functions,             |
   |            | Mixed Linear Arithmetic                      |
   +------------+----------------------------------------------+
   | QF_BVLRA   | Bitvectors, Linear Real Arithmetic           |
   |            |                                              |
   +------------+----------------------------------------------+
   | QF_LIRA    | Mixed Linear Arithmetic                      |
   |            |                                              |
   +------------+----------------------------------------------+
   | QF_UFLIRA  | Uninterpreted Functions and                  |
   |            | Mixed Linear Arithmetic                      |
   +------------+----------------------------------------------+
   | QF_UFRDL   | Uninterpreted Functions and                  |
   |            | Real Difference Logic                        |
   +------------+----------------------------------------------+
