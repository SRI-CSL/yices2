:tocdepth: 2

.. _yices_language:

Yices Input Language
====================

The language grammar is shown below

.. productionlist::
   command :   ( define-type <symbol> )
           : | ( define-type <symbol> `typedef` )
           : | ( define <symbol> :: `type` )
           : | ( define <symbol> :: `type` `expr` )
           : | ( assert `expr` )
	   : | ( assert `expr` <symbol> )
           : | ( exit )
           : | ( check )
	   : | ( check-assuming `assumptions` )
           : | ( ef-solve )
           : | ( push )
           : | ( pop )
           : | ( reset )
           : | ( show-model )
	   : | ( show-reduced-model )
           : | ( show-implicant )
	   : | ( show-unsat-core )
	   : | ( show-unsat-assumptions )
           : | ( eval `expr` )
           : | ( echo <string> )
           : | ( include <string> )
           : | ( set-param <symbol> `immediatevalue` )
	   : | ( show-param <symbol> )
	   : | ( show-params )
	   : | ( show-stats )
           : | ( reset-stats )
	   : | ( set-timeout `number` )
           : | ( show-timeout )
           : | ( export-to-dimacs <string> )
           : | ( dump-context )
	   : | ( help )
           : | ( help <symbol> )
           : | ( help <string> )
           :
   typedef :   `type`
           : | ( scalar <symbol> ... <symbol> )
           :
   type    :   <symbol>
           : | ( tuple `type` ... `type` )
           : | ( -> `type` ... `type` `type` )
           : | ( bitvector <rational> )
           : | int
           : | bool
           : | real
           :
   expr    :   true
	   : | false
           : | <symbol>
           : | `number`
           : | <binarybv>
           : | <hexabv>
           : | ( forall ( `var_decl` ... `var_decl` ) `expr` )
           : | ( exists ( `var_decl` ... `var_decl` ) `expr` )
	   : | ( lambda ( `var_decl` ... `var_decl` ) `expr` )
           : | ( let ( `binding` ... `binding` ) `expr` )
           : | ( update `expr` ( `expr` ... `expr` ) `expr` )
           : | ( `function` `expr` ... `expr` )
           :
   function :   <function-keyword>
            : | `expr`
            :
   var_decl : <symbol> :: `type`
            :
   binding  : ( <symbol> `expr` )
            :
   immediatevalue :   true
                  : | false
                  : | `number`
                  : | <symbol>
                  :
   number : <rational> | <float>
          :
   assumptions :
               : | <symbol> `assumptions`
	       : | ( not <symbol> ) `assumptions`
