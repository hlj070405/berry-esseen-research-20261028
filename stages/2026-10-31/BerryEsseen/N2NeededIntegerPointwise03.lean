module

public import BerryEsseen.N2NeededIntegerData
public import BerryEsseen.N2IntegerPointwiseReplay

@[expose] public section

/-! 2026-10-29: integer power numerators and the unchanged original
rows020..024 closed trees. The entries equality is the semantic cache bridge.
No Bernstein coefficient or host closed flag is a premise. -/

namespace BerryEsseen.N2NeededIntegerPointwise03

open N2NeededData N2NeededIntegerData N2IntegerBernstein
  N2IntegerRectangleCertificate N2MajorantPolynomials

def rowIndex (j : Fin 5) : Fin 65 :=
  ⟨3 * 5 + j.val,
    lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (3 * 5)) (by decide)⟩

def signX : Fin 4 → ℚ := N2IntegerPointwiseReplay.signX
def signY : Fin 4 → ℚ := N2IntegerPointwiseReplay.signY

def powers : Fin 5 → Fin 4 → IntPower :=
  ![
    ![
      ![![(87833267493164 : ℤ), (-206501589877500 : ℤ), (161242905864625 : ℤ), (13869509818750 : ℤ)],
        ![(-206501589877500 : ℤ), (223484416850250 : ℤ), (31887920955000 : ℤ), (-48133212522625 : ℤ)],
        ![(161242905864625 : ℤ), (31887920955000 : ℤ), (-339751421246125 : ℤ), (-80322828827375 : ℤ)],
        ![(13869509818750 : ℤ), (-48133212522625 : ℤ), (-80322828827375 : ℤ), (893039191500 : ℤ)]],
      ![![(87833267493164 : ℤ), (-206501589877500 : ℤ), (161242905864625 : ℤ), (-17036846991500 : ℤ)],
        ![(-206501589877500 : ℤ), (223484416850250 : ℤ), (31887920955000 : ℤ), (-38200725042875 : ℤ)],
        ![(161242905864625 : ℤ), (31887920955000 : ℤ), (-339751421246125 : ℤ), (97106958122875 : ℤ)],
        ![(13869509818750 : ℤ), (-48133212522625 : ℤ), (-80322828827375 : ℤ), (-784952396250 : ℤ)]],
      ![![(87833267493164 : ℤ), (-206501589877500 : ℤ), (161242905864625 : ℤ), (13869509818750 : ℤ)],
        ![(-206501589877500 : ℤ), (223484416850250 : ℤ), (31887920955000 : ℤ), (-48133212522625 : ℤ)],
        ![(161242905864625 : ℤ), (31887920955000 : ℤ), (-339751421246125 : ℤ), (-80322828827375 : ℤ)],
        ![(-17036846991500 : ℤ), (-38200725042875 : ℤ), (97106958122875 : ℤ), (-784952396250 : ℤ)]],
      ![![(87833267493164 : ℤ), (-206501589877500 : ℤ), (161242905864625 : ℤ), (-17036846991500 : ℤ)],
        ![(-206501589877500 : ℤ), (223484416850250 : ℤ), (31887920955000 : ℤ), (-38200725042875 : ℤ)],
        ![(161242905864625 : ℤ), (31887920955000 : ℤ), (-339751421246125 : ℤ), (97106958122875 : ℤ)],
        ![(-17036846991500 : ℤ), (-38200725042875 : ℤ), (97106958122875 : ℤ), (-14098781864000 : ℤ)]]],
    ![
      ![![(109998941643039 : ℤ), (-220875805049125 : ℤ), (144122272518500 : ℤ), (8993557474625 : ℤ)],
        ![(-220875805049125 : ℤ), (204111415254000 : ℤ), (57012326057250 : ℤ), (-19563600378000 : ℤ)],
        ![(144122272518500 : ℤ), (57012326057250 : ℤ), (-330163592777750 : ℤ), (-71282275693750 : ℤ)],
        ![(8993557474625 : ℤ), (-19563600378000 : ℤ), (-71282275693750 : ℤ), (283733247250 : ℤ)]],
      ![![(109998941643039 : ℤ), (-220875805049125 : ℤ), (144122272518500 : ℤ), (-13069730925875 : ℤ)],
        ![(-220875805049125 : ℤ), (204111415254000 : ℤ), (57012326057250 : ℤ), (-45607129076750 : ℤ)],
        ![(144122272518500 : ℤ), (57012326057250 : ℤ), (-330163592777750 : ℤ), (101816826273500 : ℤ)],
        ![(8993557474625 : ℤ), (-19563600378000 : ℤ), (-71282275693750 : ℤ), (-5896697386000 : ℤ)]],
      ![![(109998941643039 : ℤ), (-220875805049125 : ℤ), (144122272518500 : ℤ), (8993557474625 : ℤ)],
        ![(-220875805049125 : ℤ), (204111415254000 : ℤ), (57012326057250 : ℤ), (-19563600378000 : ℤ)],
        ![(144122272518500 : ℤ), (57012326057250 : ℤ), (-330163592777750 : ℤ), (-71282275693750 : ℤ)],
        ![(-13069730925875 : ℤ), (-45607129076750 : ℤ), (101816826273500 : ℤ), (-5896697386000 : ℤ)]],
      ![![(109998941643039 : ℤ), (-220875805049125 : ℤ), (144122272518500 : ℤ), (-13069730925875 : ℤ)],
        ![(-220875805049125 : ℤ), (204111415254000 : ℤ), (57012326057250 : ℤ), (-45607129076750 : ℤ)],
        ![(144122272518500 : ℤ), (57012326057250 : ℤ), (-330163592777750 : ℤ), (101816826273500 : ℤ)],
        ![(-13069730925875 : ℤ), (-45607129076750 : ℤ), (101816826273500 : ℤ), (-22966294647750 : ℤ)]]],
    ![
      ![![(119594781969914 : ℤ), (-240747172665750 : ℤ), (156036557638875 : ℤ), (22170070567125 : ℤ)],
        ![(-240747172665750 : ℤ), (201613957207375 : ℤ), (87116943798375 : ℤ), (-29277032534250 : ℤ)],
        ![(156036557638875 : ℤ), (87116943798375 : ℤ), (-360574820797375 : ℤ), (-95709352701125 : ℤ)],
        ![(22170070567125 : ℤ), (-29277032534250 : ℤ), (-95709352701125 : ℤ), (-610099206125 : ℤ)]],
      ![![(119594781969914 : ℤ), (-240747172665750 : ℤ), (156036557638875 : ℤ), (-12367326565875 : ℤ)],
        ![(-240747172665750 : ℤ), (201613957207375 : ℤ), (87116943798375 : ℤ), (-54563585514250 : ℤ)],
        ![(156036557638875 : ℤ), (87116943798375 : ℤ), (-360574820797375 : ℤ), (100130931870625 : ℤ)],
        ![(22170070567125 : ℤ), (-29277032534250 : ℤ), (-95709352701125 : ℤ), (4249105543625 : ℤ)]],
      ![![(119594781969914 : ℤ), (-240747172665750 : ℤ), (156036557638875 : ℤ), (22170070567125 : ℤ)],
        ![(-240747172665750 : ℤ), (201613957207375 : ℤ), (87116943798375 : ℤ), (-29277032534250 : ℤ)],
        ![(156036557638875 : ℤ), (87116943798375 : ℤ), (-360574820797375 : ℤ), (-95709352701125 : ℤ)],
        ![(-12367326565875 : ℤ), (-54563585514250 : ℤ), (100130931870625 : ℤ), (4249105543625 : ℤ)]],
      ![![(119594781969914 : ℤ), (-240747172665750 : ℤ), (156036557638875 : ℤ), (-12367326565875 : ℤ)],
        ![(-240747172665750 : ℤ), (201613957207375 : ℤ), (87116943798375 : ℤ), (-54563585514250 : ℤ)],
        ![(156036557638875 : ℤ), (87116943798375 : ℤ), (-360574820797375 : ℤ), (100130931870625 : ℤ)],
        ![(-12367326565875 : ℤ), (-54563585514250 : ℤ), (100130931870625 : ℤ), (-17524809730125 : ℤ)]]],
    ![
      ![![(168718101981914 : ℤ), (-246336150395875 : ℤ), (112641524344125 : ℤ), (23804501323500 : ℤ)],
        ![(-246336150395875 : ℤ), (172554649014750 : ℤ), (105390003849125 : ℤ), (13144165238750 : ℤ)],
        ![(112641524344125 : ℤ), (105390003849125 : ℤ), (-309399427944125 : ℤ), (-66380768278375 : ℤ)],
        ![(23804501323500 : ℤ), (13144165238750 : ℤ), (-66380768278375 : ℤ), (6053420240625 : ℤ)]],
      ![![(168718101981914 : ℤ), (-246336150395875 : ℤ), (112641524344125 : ℤ), (-3950421794750 : ℤ)],
        ![(-246336150395875 : ℤ), (172554649014750 : ℤ), (105390003849125 : ℤ), (-58202202391250 : ℤ)],
        ![(112641524344125 : ℤ), (105390003849125 : ℤ), (-309399427944125 : ℤ), (90080941147875 : ℤ)],
        ![(23804501323500 : ℤ), (13144165238750 : ℤ), (-66380768278375 : ℤ), (-19878672291875 : ℤ)]],
      ![![(168718101981914 : ℤ), (-246336150395875 : ℤ), (112641524344125 : ℤ), (23804501323500 : ℤ)],
        ![(-246336150395875 : ℤ), (172554649014750 : ℤ), (105390003849125 : ℤ), (13144165238750 : ℤ)],
        ![(112641524344125 : ℤ), (105390003849125 : ℤ), (-309399427944125 : ℤ), (-66380768278375 : ℤ)],
        ![(-3950421794750 : ℤ), (-58202202391250 : ℤ), (90080941147875 : ℤ), (-19878672291875 : ℤ)]],
      ![![(168718101981914 : ℤ), (-246336150395875 : ℤ), (112641524344125 : ℤ), (-3950421794750 : ℤ)],
        ![(-246336150395875 : ℤ), (172554649014750 : ℤ), (105390003849125 : ℤ), (-58202202391250 : ℤ)],
        ![(112641524344125 : ℤ), (105390003849125 : ℤ), (-309399427944125 : ℤ), (90080941147875 : ℤ)],
        ![(-3950421794750 : ℤ), (-58202202391250 : ℤ), (90080941147875 : ℤ), (-19385547863375 : ℤ)]]],
    ![
      ![![(190358555429664 : ℤ), (-274692273316250 : ℤ), (109198520547000 : ℤ), (24147151241250 : ℤ)],
        ![(-274692273316250 : ℤ), (128894351046375 : ℤ), (166064541626500 : ℤ), (21342377392125 : ℤ)],
        ![(109198520547000 : ℤ), (166064541626500 : ℤ), (-335496476879500 : ℤ), (-102126874816625 : ℤ)],
        ![(24147151241250 : ℤ), (21342377392125 : ℤ), (-102126874816625 : ℤ), (-2238959227625 : ℤ)]],
      ![![(190358555429664 : ℤ), (-274692273316250 : ℤ), (109198520547000 : ℤ), (1548738204000 : ℤ)],
        ![(-274692273316250 : ℤ), (128894351046375 : ℤ), (166064541626500 : ℤ), (-73612099307875 : ℤ)],
        ![(109198520547000 : ℤ), (166064541626500 : ℤ), (-335496476879500 : ℤ), (90783007131375 : ℤ)],
        ![(24147151241250 : ℤ), (21342377392125 : ℤ), (-102126874816625 : ℤ), (6814411340625 : ℤ)]],
      ![![(190358555429664 : ℤ), (-274692273316250 : ℤ), (109198520547000 : ℤ), (24147151241250 : ℤ)],
        ![(-274692273316250 : ℤ), (128894351046375 : ℤ), (166064541626500 : ℤ), (21342377392125 : ℤ)],
        ![(109198520547000 : ℤ), (166064541626500 : ℤ), (-335496476879500 : ℤ), (-102126874816625 : ℤ)],
        ![(1548738204000 : ℤ), (-73612099307875 : ℤ), (90783007131375 : ℤ), (6814411340625 : ℤ)]],
      ![![(190358555429664 : ℤ), (-274692273316250 : ℤ), (109198520547000 : ℤ), (1548738204000 : ℤ)],
        ![(-274692273316250 : ℤ), (128894351046375 : ℤ), (166064541626500 : ℤ), (-73612099307875 : ℤ)],
        ![(109198520547000 : ℤ), (166064541626500 : ℤ), (-335496476879500 : ℤ), (90783007131375 : ℤ)],
        ![(1548738204000 : ℤ), (-73612099307875 : ℤ), (90783007131375 : ℤ), (-18605434681125 : ℤ)]]]]

theorem powers_entries :
    ∀ (j : Fin 5) (o r s : Fin 4), (powers j o r s : ℚ) / (D : ℚ) =
      orthantPower (coefficients (rowIndex j)) (signX o) (signY o) (1 / 1000) r s := by
  decide +kernel

theorem powers_eq (j : Fin 5) (o : Fin 4) :
    rationalPower (powers j o) D =
      orthantPower (coefficients (rowIndex j))
        (N2IntegerPointwiseReplay.signX o) (N2IntegerPointwiseReplay.signY o) (1 / 1000) := by
  funext r s
  exact powers_entries j o r s

def trees : Fin 5 → Fin 4 → Certificate :=
  ![
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (-168 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (-156 : ℤ)
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (-162 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside))
                            Certificate.inside)
                          Certificate.inside)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      Certificate.inside)))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (-156 : ℤ)
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (-162 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside))
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside))
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                Certificate.inside)))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-528 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-432 : ℤ)
                          (Certificate.splitX (-504 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-456 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside)))
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.splitX (-432 : ℤ)
                        (Certificate.splitY (-528 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-456 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        Certificate.inside)
                      (Certificate.splitX (-432 : ℤ)
                        (Certificate.splitY (-432 : ℤ)
                          (Certificate.splitX (-456 : ℤ)
                            (Certificate.splitY (-456 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)))))
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                Certificate.inside))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (-11592448821153891 : ℤ) (45739683715481600 : ℕ) none)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-999829891358226513 : ℤ) (3602879701896396800 : ℕ) none)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-41319606077426439 : ℤ) (77405618595430400 : ℕ) none)
                          (Certificate.cross (-406639192744617381 : ℤ) (731834939447705600 : ℕ) none)))
                      (Certificate.cross (-7110349404564627 : ℤ) (12314530231091200 : ℕ) none))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-41319606077426439 : ℤ) (77405618595430400 : ℕ) none))
                        (Certificate.cross (-406639192744617381 : ℤ) (731834939447705600 : ℕ) none)))
                    (Certificate.cross (-7110349404564627 : ℤ) (12314530231091200 : ℕ) none))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-451826164471257235269 : ℤ) (749398977994450534400 : ℕ) none)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside))))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.cross (-197942621994007 : ℤ) (219902325555200 : ℕ) none)
              (Certificate.cross (-298047812681763 : ℤ) (879609302220800 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-69330654590038469 : ℤ) (112589990684262400 : ℕ) none)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.splitY (360 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside))
                        Certificate.outside))
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)))
          Certificate.outside)),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-197942621994007 : ℤ) (219902325555200 : ℕ) none)
              (Certificate.splitX (192 : ℤ)
                (Certificate.cross (-40103084282244047 : ℤ) (56294995342131200 : ℕ) none)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (360 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside))
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-298047812681763 : ℤ) (879609302220800 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          Certificate.outside)),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)))
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (360 : ℤ)
                            Certificate.outside
                            Certificate.outside)))))))
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside))
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              Certificate.outside))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (48 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (72 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (84 : ℤ)
                                Certificate.outside
                                Certificate.outside))))))
                    Certificate.outside))
                Certificate.outside))
            Certificate.outside))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (960 : ℤ)
                Certificate.outside
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (48 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (72 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (84 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))))))
                      Certificate.outside))
                  Certificate.outside))
              Certificate.outside))
          Certificate.outside))],
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            Certificate.inside)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-528 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-432 : ℤ)
                          (Certificate.splitX (-504 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          Certificate.inside)))
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.splitX (-432 : ℤ)
                        (Certificate.splitY (-528 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-456 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        Certificate.inside)
                      Certificate.inside))))
              Certificate.inside)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (-11096125688137657 : ℤ) (77405618595430400 : ℕ) none)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-1674965578883474411 : ℤ) (50440315826549555200 : ℕ) none)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-3065045884226067817 : ℤ) (6305039478318694400 : ℕ) none)
                          (Certificate.cross (-1285690679230458899 : ℤ) (2476979795053772800 : ℕ) none)))
                      (Certificate.cross (-12596825422468379 : ℤ) (22869841857740800 : ℕ) none))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.cross (-3065045884226067817 : ℤ) (6305039478318694400 : ℕ) none)
                        (Certificate.cross (-1285690679230458899 : ℤ) (2476979795053772800 : ℕ) none)))
                    (Certificate.cross (-12596825422468379 : ℤ) (22869841857740800 : ℕ) none))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.splitY (-168 : ℤ)
                              (Certificate.splitX (-180 : ℤ)
                                (Certificate.cross (-49041480252272632085831 : ℤ) (95923069183289668403200 : ℕ) none)
                                (Certificate.cross (-14090114539431740785807 : ℤ) (25825441703193372262400 : ℕ) none))
                              (Certificate.cross (-3749602080924655710179 : ℤ) (6686944726719712460800 : ℕ) none))
                            (Certificate.cross (-737491402088945578663 : ℤ) (1268213655067531673600 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside))))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            Certificate.inside
            (Certificate.splitY (384 : ℤ)
              Certificate.inside
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none))
                (Certificate.cross (-4992585962633711 : ℤ) (3518437208883200 : ℕ) none))
              (Certificate.cross (-4556942798902001 : ℤ) (12314530231091200 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-2229567436614931 : ℤ) (3518437208883200 : ℕ) none)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.splitY (360 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside))
                        Certificate.outside))
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  Certificate.outside))))
          Certificate.outside)),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            Certificate.inside
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.cross (-2964148338163001 : ℤ) (5717460464435200 : ℕ) none)
                (Certificate.cross (-2179107353273181 : ℤ) (3518437208883200 : ℕ) none))
              (Certificate.splitX (192 : ℤ)
                (Certificate.cross (-14137810253208377 : ℤ) (20231013951078400 : ℕ) none)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (360 : ℤ)
                            (Certificate.splitY (-168 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-168 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside))
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-4556942798902001 : ℤ) (12314530231091200 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside))
                Certificate.outside))))
        (Certificate.cross (-158166569724461 : ℤ) (2418925581107200 : ℕ) none)),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (144 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside))))))
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside))
                Certificate.outside)
              Certificate.outside))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (48 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (72 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (84 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (90 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))))))))
                    Certificate.outside))
                Certificate.outside))
            Certificate.outside))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (960 : ℤ)
                Certificate.outside
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (48 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (72 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (84 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (90 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))))))))
                      Certificate.outside))
                  Certificate.outside))
              Certificate.outside))
          Certificate.outside))],
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (-120 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (-108 : ℤ)
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (-114 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside))
                            Certificate.inside))
                        Certificate.inside)
                      Certificate.inside)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      Certificate.inside)))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside))))
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (-120 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (-108 : ℤ)
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (-114 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside))
                          Certificate.inside))
                      Certificate.inside)
                    Certificate.inside)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    Certificate.inside)))
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                Certificate.inside)))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-432 : ℤ)
                        (Certificate.splitY (-432 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-456 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        (Certificate.splitY (-432 : ℤ)
                          (Certificate.splitX (-408 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          Certificate.inside))))))
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    Certificate.inside)
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-545079881490602753 : ℤ) (1801439850948198400 : ℕ) none)
                          (Certificate.cross (-620385070017928891 : ℤ) (1351079888211148800 : ℕ) none)))
                      (Certificate.cross (-3651905861704793 : ℤ) (7036874417766400 : ℕ) none))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.cross (-545079881490602753 : ℤ) (1801439850948198400 : ℕ) none)
                        (Certificate.cross (-620385070017928891 : ℤ) (1351079888211148800 : ℕ) none)))
                    (Certificate.cross (-3651905861704793 : ℤ) (7036874417766400 : ℕ) none))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.splitY (-168 : ℤ)
                              (Certificate.cross (-3297986159570294330663 : ℤ) (7378697629483820646400 : ℕ) none)
                              (Certificate.cross (-1633176415112774248411 : ℤ) (3228180212899171532800 : ℕ) none))
                            (Certificate.cross (-374066059260922013567 : ℤ) (691752902764108185600 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside))))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.cross (-1408641863287063 : ℤ) (1539316278886400 : ℕ) none)
              (Certificate.cross (-5555122130473043 : ℤ) (15832967439974400 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-745244433159324003 : ℤ) (1238489897526886400 : ℕ) none)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.splitY (360 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside))
                        Certificate.outside))
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))))
          Certificate.outside)),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-1408641863287063 : ℤ) (1539316278886400 : ℕ) none)
              (Certificate.splitX (192 : ℤ)
                (Certificate.cross (-107269280735747391 : ℤ) (154811237190860800 : ℕ) none)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (360 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-168 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside))
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-5555122130473043 : ℤ) (15832967439974400 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))))
        (Certificate.cross (-136361468549043 : ℤ) (96207267430400 : ℕ) none)),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (144 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (576 : ℤ)
                Certificate.outside
                Certificate.outside)))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (108 : ℤ)
                                Certificate.outside
                                Certificate.outside))
                            Certificate.outside))
                        Certificate.outside))))
                Certificate.outside))
            Certificate.outside))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (960 : ℤ)
                Certificate.outside
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (120 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (108 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside))
                          Certificate.outside))))
                  Certificate.outside))
              Certificate.outside))
          Certificate.outside))],
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            Certificate.inside)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-432 : ℤ)
                        (Certificate.splitY (-432 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-432 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-408 : ℤ)
                            Certificate.inside
                            Certificate.inside)))))))
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    Certificate.inside)
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-171583508093746989 : ℤ) (450359962737049600 : ℕ) none))
                      (Certificate.cross (-142967265661461 : ℤ) (302365697638400 : ℕ) none))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-171583508093746989 : ℤ) (450359962737049600 : ℕ) none)))
                    (Certificate.cross (-142967265661461 : ℤ) (302365697638400 : ℕ) none))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-2490099006103883715483 : ℤ) (5995191823955604275200 : ℕ) none)
                            (Certificate.cross (-749840211118240965951 : ℤ) (1614090106449585766400 : ℕ) none))
                          (Certificate.cross (-205993937970721360197 : ℤ) (417934045419982028800 : ℕ) none))
                        (Certificate.cross (-41566319442611406759 : ℤ) (79263353441720729600 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside))))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (24 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (12 : ℤ)
                                  Certificate.inside
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside)
              Certificate.inside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-528 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-504 : ℤ)
                            (Certificate.splitY (168 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-72420026002590961197 : ℤ) (93674872249306316800 : ℕ) none))
                            (Certificate.cross (-8094942306597588317 : ℤ) (10358279142952140800 : ℕ) none)))))
                    (Certificate.cross (-2451874573487845173 : ℤ) (3152519739159347200 : ℕ) none))
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.cross (-369659293067026399 : ℤ) (450359962737049600 : ℕ) none)
                    Certificate.outside)))
              (Certificate.cross (-17903255137099629 : ℤ) (45739683715481600 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-110020054869931407 : ℤ) (154811237190860800 : ℕ) none)
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))))
          Certificate.outside)),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (24 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (12 : ℤ)
                                Certificate.inside
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                Certificate.inside))
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (-39897813928942131 : ℤ) (394064967394918400 : ℕ) none)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-528 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-471250494466486365951 : ℤ) (749398977994450534400 : ℕ) none)
                            (Certificate.cross (-3191193159621897971 : ℤ) (4053239664633446400 : ℕ) none))))
                      (Certificate.cross (-2451874573487845173 : ℤ) (3152519739159347200 : ℕ) none))))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.cross (-369659293067026399 : ℤ) (450359962737049600 : ℕ) none)
                      Certificate.outside)
                    Certificate.outside)))
              (Certificate.splitX (192 : ℤ)
                (Certificate.cross (-110020054869931407 : ℤ) (154811237190860800 : ℕ) none)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-17903255137099629 : ℤ) (45739683715481600 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))))
        (Certificate.cross (-53233458113709 : ℤ) (590987499929600 : ℕ) none)),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside)
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              Certificate.outside))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (120 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (132 : ℤ)
                                Certificate.outside
                                Certificate.outside))))
                        Certificate.outside))))
                Certificate.outside))
            Certificate.outside))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (960 : ℤ)
                Certificate.outside
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (120 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (132 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))))
                          Certificate.outside))))
                  Certificate.outside))
              Certificate.outside))
          Certificate.outside))],
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (-24 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (-12 : ℤ)
                                  Certificate.inside
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (-6 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside))
                                Certificate.inside))
                            Certificate.inside))
                        Certificate.inside))
                    Certificate.inside))
                Certificate.inside))
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (-24 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (-12 : ℤ)
                                Certificate.inside
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (-6 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside))
                              Certificate.inside))
                          Certificate.inside))
                      Certificate.inside))
                  Certificate.inside))
              Certificate.inside))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-432 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside))
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.splitX (-360 : ℤ)
                            (Certificate.splitY (-360 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.cross (-479081309556068173 : ℤ) (2251799813685248000 : ℕ) none)
                      (Certificate.cross (-3268510882987627 : ℤ) (8796093022208000 : ℕ) none))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.cross (-479081309556068173 : ℤ) (2251799813685248000 : ℕ) none)
                    (Certificate.cross (-3268510882987627 : ℤ) (8796093022208000 : ℕ) none))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-573482545298940492733 : ℤ) (2305843009213693952000 : ℕ) none)
                            (Certificate.splitY (-168 : ℤ)
                              (Certificate.cross (-573482545298940492733 : ℤ) (2305843009213693952000 : ℕ) none)
                              (Certificate.cross (-437438795523760742201 : ℤ) (1152921504606846976000 : ℕ) none)))
                          (Certificate.cross (-150616693111937942947 : ℤ) (360287970189639680000 : ℕ) none))
                        (Certificate.cross (-33786058333017197009 : ℤ) (72057594037927936000 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside))))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            Certificate.inside
            (Certificate.splitY (384 : ℤ)
              Certificate.inside
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-47969667924494407 : ℤ) (140737488355328000 : ℕ) none)
                  (Certificate.cross (-41150436760399383 : ℤ) (70368744177664000 : ℕ) none)))
              (Certificate.cross (-17973266239364129 : ℤ) (43980465111040000 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.cross (-11588585260517627 : ℤ) (13194139533312000 : ℕ) none)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))))
          Certificate.outside)),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            Certificate.inside
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.cross (-47969667924494407 : ℤ) (140737488355328000 : ℕ) none)
                (Certificate.cross (-41150436760399383 : ℤ) (70368744177664000 : ℕ) none))
              (Certificate.splitX (192 : ℤ)
                (Certificate.cross (-83245230644268141 : ℤ) (140737488355328000 : ℕ) none)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-17973266239364129 : ℤ) (43980465111040000 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (408 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))))
        (Certificate.cross (-79435730988043 : ℤ) (1168231104512000 : ℕ) none)),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)))
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)
                Certificate.outside)))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (144 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (156 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (162 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))))
                            Certificate.outside))))))
                Certificate.outside))
            Certificate.outside))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (960 : ℤ)
                Certificate.outside
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (168 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (156 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (162 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))))
                              Certificate.outside))))))
                  Certificate.outside))
              Certificate.outside))
          Certificate.outside))]]

def integerChecks (j : Fin 5) : Bool :=
  N2IntegerPointwiseReplay.fourChecks (powers j) D S (tNum (rowIndex j)) (trees j)

theorem checks : ∀ j : Fin 5, integerChecks j = true := by
  decide +kernel

theorem pointwise (j : Fin 5) (x y : ℝ) (hx : |x| ≤ 6) (hy : |y| ≤ 6) :
    N2MomentMajorant.closedIndicator (upperQ (rowIndex j) : ℝ) x y ≤
      N2MomentMajorant.majorant (coefficients (rowIndex j)) x y + (1 : ℝ) / 1000 := by
  have hp := N2IntegerPointwiseReplay.pointwise_of_fourChecks
    (coefficients (rowIndex j)) (1 / 1000) (powers j) D S (tNum (rowIndex j))
    (trees j) D_pos S_pos (powers_eq j) (checks j) x y hx hy
  rw [← upperQ_eq_tNum] at hp
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hp

end BerryEsseen.N2NeededIntegerPointwise03

#print axioms BerryEsseen.N2NeededIntegerPointwise03.powers_entries
#print axioms BerryEsseen.N2NeededIntegerPointwise03.powers_eq
#print axioms BerryEsseen.N2NeededIntegerPointwise03.checks
#print axioms BerryEsseen.N2NeededIntegerPointwise03.pointwise
