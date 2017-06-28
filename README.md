# AndOrTab
*AndOrTab is an implementation of semantic tableaux method for propositional abduction*

AndOrTab is semantic tableau based implementation for propositional abduction according to semantic minimality criteria.
The implementation includes
* Semantic tableau method in [1],
* And-Or connected semantic tableau in [2].
The work is completed during the PhD and PostDoc stay at Télécom ParisTech, funded by the ANR project LOGIMA and DigiCosme Post-Thèse Université Paris Saclay.

## Dependencies

* tweety (version 1.3) from http://tweetyproject.org/

## Input Format

The input format of a formula is encoded as follows:
!p1 || p2 && p3
p1, p2 and p3 represent _literals_
! represents the _negation_
|| represents the _disjunction_
&& represents the _conjunction_


## Usage

Example:

java -jar out/artifacts/andortab_aliseda_jar2/andortab.jar -k exampleKb.txt -o "w&&d"

-k knowledge base path
-o observation formula

out/artifacts/andortab_aliseda_jar2/andortab.jar semantic tableau method in [1]
out/artifacts/andortab_jar/andortab.jar And-Or connected semantic tableau based propositional abduction



## Reference
[1] A. Aliseda-Llera, *Seeking explanations: abduction in logic, philosophy of science and artificial intelligence*, PhD Thesis, University of Amsterdam, 1997
[2] Y. Yang, R. De Aldama, J. Atif, I. Bloch, *Efficient semantic tableau generation for abduction in propositional logic*, ECAI 2016