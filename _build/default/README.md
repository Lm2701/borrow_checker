# borrow_checker

L'ensemble des TODO a été traité, et le code passe tous les tests. 
J'ai dû modifié le fichier do_tests car sinon les erreurs des failwith n'étaient pas prises en compte.
La plus grosse difficulté que j'ai rencontrée a eu lieu lors du débuggage du code. En effet, j'ai d'abord cherché à faire un code trop complexe qui passait les tests un à un plutôt que d'essayer de trouver des erreurs globales. A la fin du projet, j'ai compris que le code que j'avais fait était parfois trop complexe et trop précis, j'ai donc cherché à le simplifier au maximum, et en faisant cela, j'ai réussi à passer tous les tests. 
Ma principale erreur était dans la génération des contraintes au niveau des reborrow car je gérais mal le cas où le borrow était une struct.

Après avoir fini le code principal, j'ai essayé de rédiger un code compilant le mir en c. Ce code se trouve dans le fichier mir_to_c.ml, mais n'est pas fonctionnel.
