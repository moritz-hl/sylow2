#Finite Sets in Lean
Finite Sets = Liste der Elemente Modulo Sortierung.
(Fintype)

-Gruppen in Lean

-Gruppenaction (Monoid Action in Lean)
+ Sätze Finxpunkt usw.



#Sylow.lean

##Imports

##Struktur

###lemma mem_fixed_points_iff_card_orbit_eq_one 

Ein Element x is ein Fixpunkt gdw #Bahn(x) = 1.

*Beweis*:
Zuerst rewrite sodass
x ist fixpunkt gdw für alle y im orbit y = x.
Dann split (gdw) über beide Richtungen.

*Hinrichtung*:



*Rückrichtung*:

Was ist subtype.mk.inj?

lemma card_modeq_card_fixed_points

Card X = card fixedPoints (mod P).



Nötige Implementierungen in FTL:

--Gruppen
--Endlichkeit + Kardinalität von Gruppen
--Faktorgruppen
--Teilbarkeit
--Primzahlen

