# friday_nigth_mood

En pleine réflexion sur un exercice de mathématique discrète concernant les langages, je me suis retrouvé à développer informellement une preuve. Pour mieux la comprendre et la maîtriser, je l'ai saisie en COQ.

## Utilisation

Le dossier `proof` contient le développement COQ. Un fichier `_CoqProject` est disponible à sa racine. Les utilisateurs de l'extension [VSCoq](https://github.com/coq-community/vscoq) peuvent donc directement charger les preuves pour travailler dessus de la manière suivante :

**[1] ouverture du dossier**
```shell
code proof
```

**[2] compilation des sources**
```
make -f CoqMakefile
```

**[3] utilisation**

Une fois les deux première commandes saisies, les modules COQ sont disponibles sous le nom `Utils`. On peut donc les importer dans un fichier du dossier proof comme suit :

```coq
Require Import Utils.
```

## Documentation

Une version HTML des sources et de leur documentation peut être générée avec la commande suivante (toujours dans le dossier `proof`) :

```shell
make -f CoqMakefile html
```





