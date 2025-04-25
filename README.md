# borrow_checker

- [ ] Task 1 : Compléter l'analyse statique dans uninitialized_places.ml
- [ ] Task 2 : Vérifier qu’aucune écriture n’a lieu sous un emprunt partagé, et qu’aucun
emprunt mutable n’est créé avec une place se trouvant sous un emprunt partagé
- [ ] Task 3 : Compléter le code responsable de la génération des contraintes, situé
dans borrowck.ml
- [ ] Task 4 : Effectuer la vérification des durées de vie
- [ ] Task 5 : Compléter l'analyseur d'emprunt
- [ ] Task 6 : Extension : Ajouter la prise en charge du sous-typage des durées de vie (par exemple, &’a i32 est un sous-type de &’b i32 dès que ’a: ’b). Comme en Rust, la variance des emprunts et des types struct doit être prise en compte.
- [ ] Task 7 : Extension : Étendre le système de types : ajouter la prise en charge des types enum, Box, du polymorphisme de types, etc.
- [ ] Task 8 : Extension : Développer un back-end qui traduit le code MiniMir en un langage bas-niveau (assembleur, Wasm, C, ...).
