This repository contains the Isabelle formalization of abstract formulations
of Gödel's Incompleteness Theorems related to the article

> **Distilling the Requirements of Gödel's Incompleteness Theorems with a Proof Assistant**
>
> Andrei Popescu, Dmitriy Traytel

The formal development can be browsed as a generated HTML page
(see the ```html``` directory). A better way to study the theory files, however, is to open
them in Isabelle/jEdit.

The raw Isabelle sources are included in a separate directory called ```thys```.

### Installation

The formalization can been processed with Isabelle2020-RC3, which can be downloaded
from

[https://isabelle.in.tum.de/website-Isabelle2020-RC3/](https://isabelle.in.tum.de/website-Isabelle2020-RC3/)

and installed following the standard instructions from

[https://isabelle.in.tum.de/website-Isabelle2020-RC3/installation.html](https://isabelle.in.tum.de/website-Isabelle2020-RC3/installation.html)

With such a cold start it takes about 20 minutes until the opened theory is
processed. With Isabelle up and running it should take only 5 minutes.

### Organization

The formalization of the abstract theory and the concrete instances is organized in four sessions
(see ROOT file):

1. ```Abstract```: contains all our abstract infrastructure and results (from paper's Sections 2 and 3).

2. ```HF_Sets_Semantic_First_and_Second```: contains the instantiation of our abstract infrastructure with Paulson's
notions stemming from his formalization of the First and Second Incompleteness theorems (from the AFP entry
Incompleteness), including the soundness assumption for the underlying theory. The instantiation
results in a reproduction of Paulson's First and Second Incompleteness theorem.

3. ```HF_Sets_Semanticless_Second```: contains the instantiation of our abstract infrastructure with an improved version
of Paulson's notions, which this time do *not* assume soundness of the underlying calculus. The instantiation
results in an upgrade of Paulson's Second Incompleteness theorem, which now supports consistent, but not
necessarily sound theory. To achieve this we have adjusted some of Paulson's theories, which are contained in ```thys/Incompleteness```.

4. ```Robinson_Arith```: contains the instantiation of the logic and arithmetic part of our abstract infrastructure
with the syntax and semantics of the Robinson Arithmetic (System Q).

The Isabelle theories containing the concrete instances
rely on an existing [Archive of Formal Proofs](https://www.isa-afp.org) (AFP) installation.
To process them, Isabelle must be invoked as follows:

```isabelle jedit -d '<path/to/afp>/thys' -d 'thys'```

where the first path points to the ```thys``` directory in the AFP installation
and the second points to the ```thys``` directory of this repository.

Acknowledgement: As noted in the paper, our instantiation to hereditarily finite sets uses
many lemmas proved by Larry Paulson. Our instantiation to System Q also adapts to the new syntax many of
Paulson's constructions and proofs using Nominal Isabelle.


### Isabelle Specifics

The reader should be able to easily recognize in our formal scripts the concepts and results
reported in the paper -- based on the aforementioned separation into sessions and guided by the
theories' self-explanatory names. Moreover, the scripts use notations similar to the paper,
with minor variations, e.g., "fmla" instead of "Fmla". (Some notation variations are pointed out
below.)

Next we list some points of difference:

1) To better manage the many assumptions, the formal theorems are organized into Isabelle locales,
again having self-explanatory names: for example, the locale ```Deduct_with_PseudoOrder```
puts together logical deduction and the order-like relation. Consequently,
to identify a theorem's assumptions we need to look at both its explicit assumptions and
its underlying locale's assumptions: for example, the theorem ```godel_rosser_first``` has
only one explicit assumption (consistency), but more assumptions coming from its locale ```Rosser_Form```.

Information about locales can be found at
[https://isabelle.in.tum.de/website-Isabelle2020-RC3/dist/Isabelle2020-RC3/doc/locales.pdf](https://isabelle.in.tum.de/website-Isabelle2020-RC3/dist/Isabelle2020-RC3/doc/locales.pdf)


2) The formal scripts are obviously much more detailed than the
proof sketches shown in the paper and in the appendix, and contain significantly more lemmas.
In particular, for our logical infrastructure (theories ```Deduction``` and ```Natural_Deduction```)
we have proved a very large amounts of facts, significantly more than we needed for the current
theorems. This was done while keeping in mind our longer-term goal of instantiating our results more
broadly, where a well developed logical infrastructure will help.

3) For the same reason (ease of future instantiation), our various types of entities (terms, numerals,
formulas, proofs, etc.) do not form entire Isabelle types, but rather subsets of types: For example,
formulas are a set "fmla" of type "'fmla set" rather than the whole type 'fmla.

4) We use curried operators rather than operators on product types.

5) In addition to Goedel's incompleteness theorems, our abstract development includes the
very related theorems of Loeb and Tarski. The latter did not make it into the paper.

6) On few occasions, we use different but quite self-explanatory notations: "prv", "pprv" and
"isTrue" for the provability, "proof of" and truth predicates; "P" and "Pf" for the representations
of "prv", "pprv"; "N" and "S" for the representations of negation and self-substitution.
We also use "double" notation for the Isabelle functions that instantiate the representation formulas
to different terms: e.g., "PP t" denotes what in the paper we would write "P(t)", namely the
formula obtained from P by substituting its single variable with the term t.

7) Here is how the paper's theorems can be found in the formal scripts. Each time, we show the formal
theorem's name (or refer to some locale instantiations) and the containing Isabelle theory.

Lemma 3:
(1) => ```ωconsistentStd1_HBL1_rev``` from theory ```Abstract_Representability```;
(2) => ```ωconsistent``` from theory ```Abstract_Models```;
(3) => ```isTrue_PP_implies_prv``` from theory ```Abstract_Model```

Lamma 4 => ```prv_prfOf```, ```prfOf_prv_Pf``` and ```not_prfOf_prv_neg_Pf```
from theory ```Standard_Models```

Prop 5 => diagonalization from Diagonalizaton

Prop 6:
Goedel sentence => ```prv_φG_eqv``` from ```Godel_Formula```;
Rosser sentence => ```prv_φR_eqv``` from ```Rosser_Formula```

Prop 7 => ```godel_first_theEasyHalf``` from ```Abstract_First_Godel```

Prop 8 => ```godel_first_theHardHalf``` from ```Abstract_First_Godel```

Theorem 9 => ```godel_first``` from ```Abstract_First_Godel```

Theorem 10 => ```godel_rosser_first``` from ```Abstract_First_Godel_Rosser```

Theorem 11 => ```godel_first_strong``` from ```Abstract_First_Godel```

Theorem 12 => ```godel_first_classic``` from ```Abstract_First_Godel```

Theorem 13 => godel_second from ```Abstract_Second_Godel```

Lemma 15 => diagonalization from Jeroslow

Theorem 16 => ```jeroslow_godel_second``` from Jeroslow

Theorem 17 => ```jeroslow_godel_second_modified``` from Jeroslow

Prop 18:
(1) => The locale instantiations from theories
```Q_Instance_Syntax_Deduction```, ```Q_Instance_Theory```;
and part of the locale instantiations from theory ```HF_Instance```;
(2) => The locale instantiations from theory```Q_Instance_Sound```;
and part of the locale instantiations from theory ```HF_Instance_Weak```

Theorem 19:
(1) => the locale instantiations from theory ```HF_Instance_Weak```;
(2) => the locale instantiations from theory ```HF_Instance```











