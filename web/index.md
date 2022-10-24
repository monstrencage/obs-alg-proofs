---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

---
Here is the documentation of the various files:

* [notations](coqdoc/Obs.notations):
  Some generic notations used throughout the development.
* [list_tools](coqdoc/Obs.list_tools):
  Generic predicates and operations on lists, and their properties.
* [decidable_prop](coqdoc/Obs.decidable_prop):
  Type class for decidable properties, with automated tactics.
* [list_dec](coqdoc/Obs.list_dec):
  Further predicates, operations and properties of lists over decidable types.
* [coherence_graph](coqdoc/Obs.coherence_graph):
  Here we define coherence graphs, and their cliques. Special attention is given to the decidability properties of the model.
* [syntax_obs](coqdoc/Obs.syntax_obs):
  Syntax of propositional logic.
* [equiv_obs](coqdoc/Obs.equiv_obs):
  Axiomatisation of Observation algebra, i.e. modular definition of an equivalence relation over our syntax, with some generic axioms.
* [laws](coqdoc/Obs.laws):
  Consequences of the axioms presented in [equiv_obs](coqdoc/Obs.equiv_obs).
* [sem_obs](coqdoc/Obs.sem_obs):
  Interpretation of propositional logic sentences as closed sets of cliques of some graph. In this files we also prove the soundness of the axioms presented so far.
* [fan](coqdoc/Obs.fan):
  Definition of the finite antineighbourhood property (FAN), and completeness proof for the associated axiomatisation.
* [anticlique](coqdoc/Obs.anticlique):
  Definition of the infinite decidable anticlique graph, and completeness proof for the associated axiomatisation.
* [product](coqdoc/Obs.product):
  Definition of the product of a family of graphs, and completeness proof for the associated axiomatisation.
* [fin_sem_obs](coqdoc/Obs.fin_sem_obs):
  For FAN graphs, it is equivalent to interpret sentences as sets of _finite_ cliques.