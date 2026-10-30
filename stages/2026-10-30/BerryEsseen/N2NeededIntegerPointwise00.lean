module

public import BerryEsseen.N2NeededIntegerData
public import BerryEsseen.N2IntegerPointwiseReplay

@[expose] public section

/-! 2026-10-29: integer power numerators and the unchanged original
rows005..009 closed trees. The entries equality is the semantic cache bridge.
No Bernstein coefficient or host closed flag is a premise. -/

namespace BerryEsseen.N2NeededIntegerPointwise00

open N2NeededData N2NeededIntegerData N2IntegerBernstein
  N2IntegerRectangleCertificate N2MajorantPolynomials

def rowIndex (j : Fin 5) : Fin 65 :=
  ⟨0 * 5 + j.val,
    lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (0 * 5)) (by decide)⟩

def signX : Fin 4 → ℚ := N2IntegerPointwiseReplay.signX
def signY : Fin 4 → ℚ := N2IntegerPointwiseReplay.signY

def powers : Fin 5 → Fin 4 → IntPower :=
  ![
    ![
      ![![(38986635404414 : ℤ), (-14896399865625 : ℤ), (-32519706970375 : ℤ), (-65348593759875 : ℤ)],
        ![(-14896399865625 : ℤ), (73109212536500 : ℤ), (-117034001444250 : ℤ), (-1046904502000 : ℤ)],
        ![(-32519706970375 : ℤ), (-117034001444250 : ℤ), (129254595948375 : ℤ), (77507537857500 : ℤ)],
        ![(-65348593759875 : ℤ), (-1046904502000 : ℤ), (77507537857500 : ℤ), (26989662958750 : ℤ)]],
      ![![(38986635404414 : ℤ), (-14896399865625 : ℤ), (-32519706970375 : ℤ), (31855959307625 : ℤ)],
        ![(-14896399865625 : ℤ), (73109212536500 : ℤ), (-117034001444250 : ℤ), (52015144775750 : ℤ)],
        ![(-32519706970375 : ℤ), (-117034001444250 : ℤ), (129254595948375 : ℤ), (-43652843441000 : ℤ)],
        ![(-65348593759875 : ℤ), (-1046904502000 : ℤ), (77507537857500 : ℤ), (-47676063778000 : ℤ)]],
      ![![(38986635404414 : ℤ), (-14896399865625 : ℤ), (-32519706970375 : ℤ), (-65348593759875 : ℤ)],
        ![(-14896399865625 : ℤ), (73109212536500 : ℤ), (-117034001444250 : ℤ), (-1046904502000 : ℤ)],
        ![(-32519706970375 : ℤ), (-117034001444250 : ℤ), (129254595948375 : ℤ), (77507537857500 : ℤ)],
        ![(31855959307625 : ℤ), (52015144775750 : ℤ), (-43652843441000 : ℤ), (-47676063778000 : ℤ)]],
      ![![(38986635404414 : ℤ), (-14896399865625 : ℤ), (-32519706970375 : ℤ), (31855959307625 : ℤ)],
        ![(-14896399865625 : ℤ), (73109212536500 : ℤ), (-117034001444250 : ℤ), (52015144775750 : ℤ)],
        ![(-32519706970375 : ℤ), (-117034001444250 : ℤ), (129254595948375 : ℤ), (-43652843441000 : ℤ)],
        ![(31855959307625 : ℤ), (52015144775750 : ℤ), (-43652843441000 : ℤ), (9910768123750 : ℤ)]]],
    ![
      ![![(28934655856039 : ℤ), (-16212727664750 : ℤ), (-19407849228500 : ℤ), (-64908970744625 : ℤ)],
        ![(-16212727664750 : ℤ), (78499503013625 : ℤ), (-123029674680375 : ℤ), (-1498058047500 : ℤ)],
        ![(-19407849228500 : ℤ), (-123029674680375 : ℤ), (122360751612125 : ℤ), (79556376708125 : ℤ)],
        ![(-64908970744625 : ℤ), (-1498058047500 : ℤ), (79556376708125 : ℤ), (28380146191125 : ℤ)]],
      ![![(28934655856039 : ℤ), (-16212727664750 : ℤ), (-19407849228500 : ℤ), (33368842134625 : ℤ)],
        ![(-16212727664750 : ℤ), (78499503013625 : ℤ), (-123029674680375 : ℤ), (54318933081250 : ℤ)],
        ![(-19407849228500 : ℤ), (-123029674680375 : ℤ), (122360751612125 : ℤ), (-49574515597875 : ℤ)],
        ![(-64908970744625 : ℤ), (-1498058047500 : ℤ), (79556376708125 : ℤ), (-52706734930125 : ℤ)]],
      ![![(28934655856039 : ℤ), (-16212727664750 : ℤ), (-19407849228500 : ℤ), (-64908970744625 : ℤ)],
        ![(-16212727664750 : ℤ), (78499503013625 : ℤ), (-123029674680375 : ℤ), (-1498058047500 : ℤ)],
        ![(-19407849228500 : ℤ), (-123029674680375 : ℤ), (122360751612125 : ℤ), (79556376708125 : ℤ)],
        ![(33368842134625 : ℤ), (54318933081250 : ℤ), (-49574515597875 : ℤ), (-52706734930125 : ℤ)]],
      ![![(28934655856039 : ℤ), (-16212727664750 : ℤ), (-19407849228500 : ℤ), (33368842134625 : ℤ)],
        ![(-16212727664750 : ℤ), (78499503013625 : ℤ), (-123029674680375 : ℤ), (54318933081250 : ℤ)],
        ![(-19407849228500 : ℤ), (-123029674680375 : ℤ), (122360751612125 : ℤ), (-49574515597875 : ℤ)],
        ![(33368842134625 : ℤ), (54318933081250 : ℤ), (-49574515597875 : ℤ), (13630793189125 : ℤ)]]],
    ![
      ![![(30115817371039 : ℤ), (-24510578066750 : ℤ), (-14623887498375 : ℤ), (-66423636263375 : ℤ)],
        ![(-24510578066750 : ℤ), (91659062875750 : ℤ), (-119402975895875 : ℤ), (-1436735254375 : ℤ)],
        ![(-14623887498375 : ℤ), (-119402975895875 : ℤ), (133870489488125 : ℤ), (92495728787375 : ℤ)],
        ![(-66423636263375 : ℤ), (-1436735254375 : ℤ), (92495728787375 : ℤ), (35554949294625 : ℤ)]],
      ![![(30115817371039 : ℤ), (-24510578066750 : ℤ), (-14623887498375 : ℤ), (32857874529875 : ℤ)],
        ![(-24510578066750 : ℤ), (91659062875750 : ℤ), (-119402975895875 : ℤ), (50313487187375 : ℤ)],
        ![(-14623887498375 : ℤ), (-119402975895875 : ℤ), (133870489488125 : ℤ), (-63462267975875 : ℤ)],
        ![(-66423636263375 : ℤ), (-1436735254375 : ℤ), (92495728787375 : ℤ), (-64295471457125 : ℤ)]],
      ![![(30115817371039 : ℤ), (-24510578066750 : ℤ), (-14623887498375 : ℤ), (-66423636263375 : ℤ)],
        ![(-24510578066750 : ℤ), (91659062875750 : ℤ), (-119402975895875 : ℤ), (-1436735254375 : ℤ)],
        ![(-14623887498375 : ℤ), (-119402975895875 : ℤ), (133870489488125 : ℤ), (92495728787375 : ℤ)],
        ![(32857874529875 : ℤ), (50313487187375 : ℤ), (-63462267975875 : ℤ), (-64295471457125 : ℤ)]],
      ![![(30115817371039 : ℤ), (-24510578066750 : ℤ), (-14623887498375 : ℤ), (32857874529875 : ℤ)],
        ![(-24510578066750 : ℤ), (91659062875750 : ℤ), (-119402975895875 : ℤ), (50313487187375 : ℤ)],
        ![(-14623887498375 : ℤ), (-119402975895875 : ℤ), (133870489488125 : ℤ), (-63462267975875 : ℤ)],
        ![(32857874529875 : ℤ), (50313487187375 : ℤ), (-63462267975875 : ℤ), (23660593145625 : ℤ)]]],
    ![
      ![![(51297229765539 : ℤ), (-24566810696375 : ℤ), (-37482271332125 : ℤ), (-76877577194500 : ℤ)],
        ![(-24566810696375 : ℤ), (98604031798250 : ℤ), (-128855442534000 : ℤ), (-3977874436500 : ℤ)],
        ![(-37482271332125 : ℤ), (-128855442534000 : ℤ), (163105439760125 : ℤ), (104409989788500 : ℤ)],
        ![(-76877577194500 : ℤ), (-3977874436500 : ℤ), (104409989788500 : ℤ), (40359654519750 : ℤ)]],
      ![![(51297229765539 : ℤ), (-24566810696375 : ℤ), (-37482271332125 : ℤ), (33504049481500 : ℤ)],
        ![(-24566810696375 : ℤ), (98604031798250 : ℤ), (-128855442534000 : ℤ), (53297629886000 : ℤ)],
        ![(-37482271332125 : ℤ), (-128855442534000 : ℤ), (163105439760125 : ℤ), (-60078437390500 : ℤ)],
        ![(-76877577194500 : ℤ), (-3977874436500 : ℤ), (104409989788500 : ℤ), (-64241728330750 : ℤ)]],
      ![![(51297229765539 : ℤ), (-24566810696375 : ℤ), (-37482271332125 : ℤ), (-76877577194500 : ℤ)],
        ![(-24566810696375 : ℤ), (98604031798250 : ℤ), (-128855442534000 : ℤ), (-3977874436500 : ℤ)],
        ![(-37482271332125 : ℤ), (-128855442534000 : ℤ), (163105439760125 : ℤ), (104409989788500 : ℤ)],
        ![(33504049481500 : ℤ), (53297629886000 : ℤ), (-60078437390500 : ℤ), (-64241728330750 : ℤ)]],
      ![![(51297229765539 : ℤ), (-24566810696375 : ℤ), (-37482271332125 : ℤ), (33504049481500 : ℤ)],
        ![(-24566810696375 : ℤ), (98604031798250 : ℤ), (-128855442534000 : ℤ), (53297629886000 : ℤ)],
        ![(-37482271332125 : ℤ), (-128855442534000 : ℤ), (163105439760125 : ℤ), (-60078437390500 : ℤ)],
        ![(33504049481500 : ℤ), (53297629886000 : ℤ), (-60078437390500 : ℤ), (17005131288750 : ℤ)]]],
    ![
      ![![(2879910473914 : ℤ), (-18751197228125 : ℤ), (71705357492750 : ℤ), (-33618113638750 : ℤ)],
        ![(-18751197228125 : ℤ), (132494387571500 : ℤ), (-181454049436750 : ℤ), (-60425615535500 : ℤ)],
        ![(71705357492750 : ℤ), (-181454049436750 : ℤ), (-108307743305375 : ℤ), (-17978495819750 : ℤ)],
        ![(-33618113638750 : ℤ), (-60425615535500 : ℤ), (-17978495819750 : ℤ), (-1824669571625 : ℤ)]],
      ![![(2879910473914 : ℤ), (-18751197228125 : ℤ), (71705357492750 : ℤ), (-412509318250 : ℤ)],
        ![(-18751197228125 : ℤ), (132494387571500 : ℤ), (-181454049436750 : ℤ), (65613579064000 : ℤ)],
        ![(71705357492750 : ℤ), (-181454049436750 : ℤ), (-108307743305375 : ℤ), (60204687375500 : ℤ)],
        ![(-33618113638750 : ℤ), (-60425615535500 : ℤ), (-17978495819750 : ℤ), (10040051128125 : ℤ)]],
      ![![(2879910473914 : ℤ), (-18751197228125 : ℤ), (71705357492750 : ℤ), (-33618113638750 : ℤ)],
        ![(-18751197228125 : ℤ), (132494387571500 : ℤ), (-181454049436750 : ℤ), (-60425615535500 : ℤ)],
        ![(71705357492750 : ℤ), (-181454049436750 : ℤ), (-108307743305375 : ℤ), (-17978495819750 : ℤ)],
        ![(-412509318250 : ℤ), (65613579064000 : ℤ), (60204687375500 : ℤ), (10040051128125 : ℤ)]],
      ![![(2879910473914 : ℤ), (-18751197228125 : ℤ), (71705357492750 : ℤ), (-412509318250 : ℤ)],
        ![(-18751197228125 : ℤ), (132494387571500 : ℤ), (-181454049436750 : ℤ), (65613579064000 : ℤ)],
        ![(71705357492750 : ℤ), (-181454049436750 : ℤ), (-108307743305375 : ℤ), (60204687375500 : ℤ)],
        ![(-412509318250 : ℤ), (65613579064000 : ℤ), (60204687375500 : ℤ), (-19229023196625 : ℤ)]]]]

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
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (-528 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (-552 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (-564 : ℤ)
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (-570 : ℤ)
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
                    Certificate.inside))
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (-528 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (-552 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (-564 : ℤ)
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (-570 : ℤ)
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
                  Certificate.inside))
              Certificate.inside)
            Certificate.inside)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.cross (-85197244119692907 : ℤ) (91479367430963200 : ℕ) none)
                    (Certificate.cross (-737919304695001 : ℤ) (659706976665600 : ℕ) none)))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-113203145715234189 : ℤ) (112589990684262400 : ℕ) none))
                    (Certificate.cross (-63243245076201377 : ℤ) (56294995342131200 : ℕ) none))))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.cross (-1878592902226282509 : ℤ) (1801439850948198400 : ℕ) none)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-29446858041314116649 : ℤ) (28823037615171174400 : ℕ) none)
                          (Certificate.cross (-44668098819974296411 : ℤ) (43234556422756761600 : ℕ) none))))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-29446858041314116649 : ℤ) (28823037615171174400 : ℕ) none))
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.cross (-7243183472034287881 : ℤ) (7205759403792793600 : ℕ) none)
                          (Certificate.cross (-44668098819974296411 : ℤ) (43234556422756761600 : ℕ) none)))
                      (Certificate.cross (-962944447216412657 : ℤ) (900719925474099200 : ℕ) none)))
                  (Certificate.cross (-63454434251157657 : ℤ) (56294995342131200 : ℕ) none))
                (Certificate.cross (-6053434552939543 : ℤ) (5277655813324800 : ℕ) none)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-816 : ℤ)
                        (Certificate.cross (-195134670874429173 : ℤ) (225179981368524800 : ℕ) none)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-792 : ℤ)
                            (Certificate.cross (-130568280999690530163 : ℤ) (201761263306198220800 : ℕ) none)
                            (Certificate.splitY (216 : ℤ)
                              (Certificate.splitX (-780 : ℤ)
                                Certificate.inside
                                (Certificate.splitY (204 : ℤ)
                                  Certificate.inside
                                  (Certificate.cross (-138298875115129219 : ℤ) (112589990684262400 : ℕ) none)))
                              (Certificate.cross (-952643620793905923 : ℤ) (788129934789836800 : ℕ) none)))
                          (Certificate.cross (-316011511692635631 : ℤ) (309622474381721600 : ℕ) none)))
                      (Certificate.cross (-44790868886943657 : ℤ) (91479367430963200 : ℕ) none)))))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-4470796549248297 : ℤ) (3518437208883200 : ℕ) none))
                    (Certificate.cross (-37715756454051001 : ℤ) (28147497671065600 : ℕ) none))
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-744 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              (Certificate.cross (-36505781905282131 : ℤ) (28147497671065600 : ℕ) none)
                              Certificate.outside)
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-1970253223639181 : ℤ) (1759218604441600 : ℕ) none)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside))))
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-228 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (-222 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))))
                            Certificate.outside))))))
                Certificate.outside))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-960 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-864 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-816 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.splitY (-792 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (204 : ℤ)
                                Certificate.inside
                                (Certificate.cross (-138298875115129219 : ℤ) (112589990684262400 : ℕ) none)))
                            (Certificate.cross (-952643620793905923 : ℤ) (788129934789836800 : ℕ) none)))
                        (Certificate.cross (-316011511692635631 : ℤ) (309622474381721600 : ℕ) none)))
                    (Certificate.cross (-44790868886943657 : ℤ) (91479367430963200 : ℕ) none)))))
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (-26732451978602481 : ℤ) (28147497671065600 : ℕ) none)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.cross (-4470796549248297 : ℤ) (3518437208883200 : ℕ) none)
                      (Certificate.cross (-522351538004163381 : ℤ) (450359962737049600 : ℕ) none)))
                  (Certificate.cross (-1970253223639181 : ℤ) (1759218604441600 : ℕ) none))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-720 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.cross (-36505781905282131 : ℤ) (28147497671065600 : ℕ) none)
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    Certificate.outside)))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    Certificate.outside)
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1392 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-228 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (-222 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))))
                              Certificate.outside))))))
                  Certificate.outside)))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)))
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              Certificate.outside))
          Certificate.outside)
        (Certificate.splitY (768 : ℤ)
          Certificate.outside
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (864 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1056 : ℤ)
                      (Certificate.splitX (912 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1008 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)))
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (864 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1008 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    Certificate.outside)
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (1056 : ℤ)
                      (Certificate.splitX (1008 : ℤ)
                        (Certificate.splitY (1008 : ℤ)
                          (Certificate.splitX (984 : ℤ)
                            (Certificate.splitY (984 : ℤ)
                              (Certificate.splitX (972 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              Certificate.outside)
                            (Certificate.splitY (984 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)))
              Certificate.outside)
            (Certificate.splitY (1152 : ℤ)
              Certificate.outside
              Certificate.outside))))],
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (-528 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (-552 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (-564 : ℤ)
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (-570 : ℤ)
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
                    Certificate.inside))
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (-528 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (-552 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (-564 : ℤ)
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (-570 : ℤ)
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
                  Certificate.inside))
              Certificate.inside)
            Certificate.inside)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.cross (-1492764434094751 : ℤ) (1319413953331200 : ℕ) none))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.cross (-1492764434094751 : ℤ) (1319413953331200 : ℕ) none)))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.cross (-12389884923148096009 : ℤ) (12610078956637388800 : ℕ) none)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-103154698614171984197 : ℤ) (100880631653099110400 : ℕ) none)
                          (Certificate.cross (-52669286486711026161 : ℤ) (50440315826549555200 : ℕ) none))))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-103154698614171984197 : ℤ) (100880631653099110400 : ℕ) none)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.cross (-12389884923148096009 : ℤ) (12610078956637388800 : ℕ) none)
                          (Certificate.cross (-52669286486711026161 : ℤ) (50440315826549555200 : ℕ) none)))
                      (Certificate.cross (-2064503732404766317 : ℤ) (1801439850948198400 : ℕ) none)))
                  (Certificate.cross (-33485025103648813 : ℤ) (28147497671065600 : ℕ) none))
                (Certificate.cross (-68464227684545141 : ℤ) (56294995342131200 : ℕ) none)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-816 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-792 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-254571664376945399 : ℤ) (225179981368524800 : ℕ) none)))
                          (Certificate.cross (-184080855155439631 : ℤ) (197032483697459200 : ℕ) none)))
                      (Certificate.cross (-27379564166744657 : ℤ) (77405618595430400 : ℕ) none)))))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.cross (-8888945558359657 : ℤ) (7036874417766400 : ℕ) none)
                    (Certificate.cross (-439385112192116131 : ℤ) (337769972052787200 : ℕ) none))
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-744 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              (Certificate.splitX (-756 : ℤ)
                                (Certificate.splitY (204 : ℤ)
                                  Certificate.inside
                                  (Certificate.cross (-293328534090719308918949 : ℤ) (236118324143482260684800 : ℕ) none))
                                (Certificate.cross (-2451229901886599937163 : ℤ) (1844674407370955161600 : ℕ) none))
                              (Certificate.cross (-214478502930206312317 : ℤ) (172938225691027046400 : ℕ) none))
                            (Certificate.cross (-119924044572765788971 : ℤ) (86469112845513523200 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-254000016078575939 : ℤ) (225179981368524800 : ℕ) none)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside))))
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-228 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (-222 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))))
                            Certificate.outside))))))
                Certificate.outside))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-960 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-864 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-816 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (216 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-254571664376945399 : ℤ) (225179981368524800 : ℕ) none)))
                        (Certificate.cross (-184080855155439631 : ℤ) (197032483697459200 : ℕ) none)))
                    (Certificate.cross (-27379564166744657 : ℤ) (77405618595430400 : ℕ) none)))))
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (-4361612612680707173 : ℤ) (4953959590107545600 : ℕ) none)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.cross (-8888945558359657 : ℤ) (7036874417766400 : ℕ) none)
                      (Certificate.cross (-5748737165464660173 : ℤ) (4953959590107545600 : ℕ) none)))
                  (Certificate.cross (-254000016078575939 : ℤ) (225179981368524800 : ℕ) none))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-720 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.splitY (-744 : ℤ)
                              (Certificate.splitX (204 : ℤ)
                                (Certificate.cross (-232488403604326169290037 : ℤ) (191846138366579336806400 : ℕ) none)
                                (Certificate.cross (-949146606892145164527 : ℤ) (749398977994450534400 : ℕ) none))
                              (Certificate.cross (-1773613551700570334411 : ℤ) (1383505805528216371200 : ℕ) none))
                            (Certificate.cross (-6858550002574715131 : ℤ) (5404319552844595200 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    Certificate.outside)))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    Certificate.outside)
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1392 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-228 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (-222 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))))
                              Certificate.outside))))))
                  Certificate.outside)))))),
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
                      (Certificate.splitX (240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)))
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (576 : ℤ)
                Certificate.outside
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (672 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (720 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (720 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (744 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (744 : ℤ)
                              Certificate.outside
                              Certificate.outside))))))))))
          (Certificate.splitX (384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (576 : ℤ)
                Certificate.outside
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (672 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (864 : ℤ)
                      (Certificate.splitX (720 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside))
                  Certificate.outside))
              Certificate.outside)))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (864 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (816 : ℤ)
                        (Certificate.splitY (720 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    Certificate.outside))
                Certificate.outside))
            Certificate.outside)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (864 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  Certificate.outside)
                Certificate.outside)
              Certificate.outside)
            Certificate.outside)))],
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (-528 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (-504 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (-516 : ℤ)
                                  Certificate.inside
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside))
                        Certificate.inside)
                      Certificate.inside)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      Certificate.inside)))
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (-528 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (-504 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (-516 : ℤ)
                                Certificate.inside
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside))
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside))
              Certificate.inside)
            Certificate.inside)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.cross (-5924684231476627 : ℤ) (6157265115545600 : ℕ) none))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.cross (-5924684231476627 : ℤ) (6157265115545600 : ℕ) none)))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.cross (-4222384218055886509 : ℤ) (5404319552844595200 : ℕ) none)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-41031532263511453697 : ℤ) (43234556422756761600 : ℕ) none)
                          (Certificate.cross (-14437401818439513509 : ℤ) (14411518807585587200 : ℕ) none))))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-41031532263511453697 : ℤ) (43234556422756761600 : ℕ) none)
                        (Certificate.cross (-702088637653083673 : ℤ) (675539944105574400 : ℕ) none))
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-44506445589110589697 : ℤ) (43234556422756761600 : ℕ) none)
                          Certificate.outside)
                        Certificate.outside)))
                  (Certificate.cross (-68706482991602439 : ℤ) (56294995342131200 : ℕ) none))
                (Certificate.cross (-60989685061823891 : ℤ) (49258120924364800 : ℕ) none)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-816 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-15807963974903753 : ℤ) (42221246506598400 : ℕ) none)
                          (Certificate.cross (-30603976677068439 : ℤ) (56294995342131200 : ℕ) none)))
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)))))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.cross (-137424518642092503 : ℤ) (112589990684262400 : ℕ) none)
                    (Certificate.cross (-273488315346054881 : ℤ) (225179981368524800 : ℕ) none))
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-744 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              (Certificate.splitX (-756 : ℤ)
                                Certificate.inside
                                (Certificate.splitY (204 : ℤ)
                                  Certificate.inside
                                  (Certificate.cross (-31859845429456697793853 : ℤ) (25825441703193372262400 : ℕ) none)))
                              (Certificate.cross (-26713955197360117271989 : ℤ) (22136092888451461939200 : ℕ) none))
                            (Certificate.splitY (216 : ℤ)
                              (Certificate.cross (-643236279012072565233 : ℤ) (461168601842738790400 : ℕ) none)
                              Certificate.outside))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-219329797792980689 : ℤ) (197032483697459200 : ℕ) none)
                  Certificate.outside))
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-228 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (-222 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))))
                            Certificate.outside))))))
                Certificate.outside))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-960 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-864 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.cross (-15807963974903753 : ℤ) (42221246506598400 : ℕ) none)
                        (Certificate.cross (-30603976677068439 : ℤ) (56294995342131200 : ℕ) none)))
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)))))
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (-2905867125455958173 : ℤ) (4053239664633446400 : ℕ) none)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.cross (-137424518642092503 : ℤ) (112589990684262400 : ℕ) none)
                      (Certificate.cross (-4615910739763573673 : ℤ) (4053239664633446400 : ℕ) none)))
                  (Certificate.cross (-219329797792980689 : ℤ) (197032483697459200 : ℕ) none))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-720 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.splitY (-744 : ℤ)
                              (Certificate.splitX (204 : ℤ)
                                Certificate.inside
                                (Certificate.cross (-31859845429456697793853 : ℤ) (25825441703193372262400 : ℕ) none))
                              (Certificate.cross (-643236279012072565233 : ℤ) (461168601842738790400 : ℕ) none))
                            (Certificate.cross (-197955432734801560019 : ℤ) (158526706883441459200 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (240 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1392 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-228 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (-222 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))))
                              Certificate.outside))))))
                  Certificate.outside)))))),
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
                      (Certificate.splitX (240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside))))
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (528 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          (Certificate.splitX (504 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside)))
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    Certificate.outside))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))))
          (Certificate.splitX (384 : ℤ)
            Certificate.outside
            Certificate.outside))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              Certificate.outside))
          Certificate.outside))],
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (-528 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (-504 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (-516 : ℤ)
                                  Certificate.inside
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (-510 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside))
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside))
                        Certificate.inside)
                      Certificate.inside)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      Certificate.inside)))
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (-528 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (-504 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (-516 : ℤ)
                                Certificate.inside
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (-510 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside))
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside))
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside))
              Certificate.inside)
            Certificate.inside)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.cross (-1415461506020269 : ℤ) (1759218604441600 : ℕ) none)
                    (Certificate.cross (-3393140476417877 : ℤ) (3078632557772800 : ℕ) none)))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.cross (-195829419994528753 : ℤ) (197032483697459200 : ℕ) none)
                    (Certificate.cross (-3464855016854627 : ℤ) (3078632557772800 : ℕ) none))))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-3779633076482098567 : ℤ) (3602879701896396800 : ℕ) none))))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-3779633076482098567 : ℤ) (3602879701896396800 : ℕ) none)))
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-60613619644960577197 : ℤ) (57646075230342348800 : ℕ) none)
                          (Certificate.cross (-33690166047546221393 : ℤ) (32425917317067571200 : ℕ) none))
                        (Certificate.cross (-11482608538691051131 : ℤ) (10808639105689190400 : ℕ) none))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.cross (-950676431377209673 : ℤ) (900719925474099200 : ℕ) none)
                        (Certificate.cross (-5678333419242698753 : ℤ) (5404319552844595200 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.cross (-44292889076536417649 : ℤ) (43234556422756761600 : ℕ) none)
                          (Certificate.cross (-16915170627577106509 : ℤ) (16212958658533785600 : ℕ) none))
                        (Certificate.cross (-1455992483658882407 : ℤ) (1351079888211148800 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-816 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-960825932309219 : ℤ) (10555311626649600 : ℕ) none)))
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)))))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.cross (-74130722521831253 : ℤ) (56294995342131200 : ℕ) none)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-1227673491513291899 : ℤ) (1576259869579673600 : ℕ) none)
                      (Certificate.cross (-282502412139959557 : ℤ) (225179981368524800 : ℕ) none)))
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-744 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-1030476538253472039697 : ℤ) (922337203685477580800 : ℕ) none))
                            (Certificate.splitY (216 : ℤ)
                              (Certificate.splitX (-732 : ℤ)
                                (Certificate.splitY (204 : ℤ)
                                  Certificate.inside
                                  (Certificate.cross (-37312000865164663679679 : ℤ) (29514790517935282585600 : ℕ) none))
                                (Certificate.cross (-1353375184323465765557 : ℤ) (922337203685477580800 : ℕ) none))
                              (Certificate.cross (-4687302504205780371983 : ℤ) (3689348814741910323200 : ℕ) none)))
                          (Certificate.cross (-864332928942839991163 : ℤ) (807045053224792883200 : ℕ) none))
                        (Certificate.cross (-8290588919652780503 : ℤ) (5404319552844595200 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-2184680131982459 : ℤ) (1759218604441600 : ℕ) none)
                  Certificate.outside))
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-204 : ℤ)
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (-210 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))
                                Certificate.outside))))))))
                Certificate.outside))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-960 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-864 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-960825932309219 : ℤ) (10555311626649600 : ℕ) none)))
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)))))
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (-1227673491513291899 : ℤ) (1576259869579673600 : ℕ) none)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.cross (-74130722521831253 : ℤ) (56294995342131200 : ℕ) none)
                      (Certificate.cross (-282502412139959557 : ℤ) (225179981368524800 : ℕ) none)))
                  (Certificate.cross (-2184680131982459 : ℤ) (1759218604441600 : ℕ) none))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-720 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.splitY (-744 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (204 : ℤ)
                                (Certificate.cross (-12557875286723543500807 : ℤ) (10145709240540253388800 : ℕ) none)
                                (Certificate.cross (-6603320651753767603591 : ℤ) (5072854620270126694400 : ℕ) none)))
                            (Certificate.cross (-18912781547183476673 : ℤ) (14411518807585587200 : ℕ) none))
                          (Certificate.cross (-20880294550820368643 : ℤ) (14411518807585587200 : ℕ) none))
                        (Certificate.cross (-1003960843422801293 : ℤ) (900719925474099200 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (240 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    Certificate.outside)
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1392 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-204 : ℤ)
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (-210 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))
                                  Certificate.outside))))))))
                  Certificate.outside)))))),
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
                      (Certificate.splitX (240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)))
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (576 : ℤ)
                Certificate.outside
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (672 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (720 : ℤ)
                        (Certificate.splitY (720 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (720 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (744 : ℤ)
                            (Certificate.splitY (744 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)))))))))
          (Certificate.splitX (384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (576 : ℤ)
                Certificate.outside
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (672 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (864 : ℤ)
                      (Certificate.splitX (720 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside))
                  Certificate.outside))
              Certificate.outside)))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (864 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (816 : ℤ)
                        (Certificate.splitY (720 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    Certificate.outside))
                Certificate.outside))
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              Certificate.outside))
          Certificate.outside))],
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (-1248 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside))
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (-1248 : ℤ)
                    Certificate.inside
                    Certificate.inside)
                  Certificate.inside))
              Certificate.inside)
            Certificate.inside)
          Certificate.inside)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.cross (-9734268095640391 : ℤ) (17592186044416000 : ℕ) none)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.cross (-263542332052564381 : ℤ) (281474976710656000 : ℕ) none)
                      (Certificate.cross (-16761995127392383 : ℤ) (17592186044416000 : ℕ) none))))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.cross (-263542332052564381 : ℤ) (281474976710656000 : ℕ) none)
                    (Certificate.cross (-2163817755134127 : ℤ) (2199023255552000 : ℕ) none))))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-2215314825105494471 : ℤ) (2251799813685248000 : ℕ) none))))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-2215314825105494471 : ℤ) (2251799813685248000 : ℕ) none)))
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-283055168870480851663 : ℤ) (288230376151711744000 : ℕ) none)
                          (Certificate.cross (-35933984705813159661 : ℤ) (36028797018963968000 : ℕ) none))
                        (Certificate.cross (-37003497102587311661 : ℤ) (36028797018963968000 : ℕ) none))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-1121907435436304822701 : ℤ) (1152921504606846976000 : ℕ) none)
                          (Certificate.cross (-70860076995687971661 : ℤ) (72057594037927936000 : ℕ) none))
                        (Certificate.cross (-18270479511391733143 : ℤ) (18014398509481984000 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.cross (-1121907435436304822701 : ℤ) (1152921504606846976000 : ℕ) none)
                          (Certificate.cross (-17944029275476146393 : ℤ) (18014398509481984000 : ℕ) none))
                        (Certificate.cross (-4592167127460849817 : ℤ) (4503599627370496000 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.cross (-274053273760043 : ℤ) (549755813888000 : ℕ) none)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.cross (-8686664004874711 : ℤ) (17592186044416000 : ℕ) none)
                (Certificate.cross (-1030028283923563 : ℤ) (1099511627776000 : ℕ) none))
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (1344 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-168 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-156 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (-150 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))))))
                        Certificate.outside))
                    Certificate.outside))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.cross (-305161857005385631 : ℤ) (1125899906842624000 : ℕ) none)
                  (Certificate.cross (-1030028283923563 : ℤ) (1099511627776000 : ℕ) none))
                (Certificate.cross (-28621298663000047 : ℤ) (35184372088832000 : ℕ) none))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (-274053273760043 : ℤ) (549755813888000 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                Certificate.outside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-168 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-156 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (-150 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))))))
                          Certificate.outside))
                      Certificate.outside)))))))),
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
                    Certificate.outside)
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside))))
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                Certificate.outside))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside)
              Certificate.outside))
          Certificate.outside)
        Certificate.outside)]]

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

end BerryEsseen.N2NeededIntegerPointwise00

#print axioms BerryEsseen.N2NeededIntegerPointwise00.powers_entries
#print axioms BerryEsseen.N2NeededIntegerPointwise00.powers_eq
#print axioms BerryEsseen.N2NeededIntegerPointwise00.checks
#print axioms BerryEsseen.N2NeededIntegerPointwise00.pointwise
