module

public import BerryEsseen.N2NeededIntegerData
public import BerryEsseen.N2IntegerPointwiseReplay

@[expose] public section

/-! 2026-10-29: integer power numerators and the unchanged original
rows065..069 closed trees. The entries equality is the semantic cache bridge.
No Bernstein coefficient or host closed flag is a premise. -/

namespace BerryEsseen.N2NeededIntegerPointwise12

open N2NeededData N2NeededIntegerData N2IntegerBernstein
  N2IntegerRectangleCertificate N2MajorantPolynomials

def rowIndex (j : Fin 5) : Fin 65 :=
  ⟨12 * 5 + j.val,
    lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (12 * 5)) (by decide)⟩

def signX : Fin 4 → ℚ := N2IntegerPointwiseReplay.signX
def signY : Fin 4 → ℚ := N2IntegerPointwiseReplay.signY

def powers : Fin 5 → Fin 4 → IntPower :=
  ![
    ![
      ![![(619291570498664 : ℤ), (-4996018065000 : ℤ), (-114245289633750 : ℤ), (-55483943083625 : ℤ)],
        ![(-4996018065000 : ℤ), (-117596982645125 : ℤ), (-111848935901250 : ℤ), (-19426540056625 : ℤ)],
        ![(-114245289633750 : ℤ), (-111848935901250 : ℤ), (8249874344500 : ℤ), (21661523928250 : ℤ)],
        ![(-55483943083625 : ℤ), (-19426540056625 : ℤ), (21661523928250 : ℤ), (9586867813375 : ℤ)]],
      ![![(619291570498664 : ℤ), (-4996018065000 : ℤ), (-114245289633750 : ℤ), (23497679214875 : ℤ)],
        ![(-4996018065000 : ℤ), (-117596982645125 : ℤ), (-111848935901250 : ℤ), (43643231960375 : ℤ)],
        ![(-114245289633750 : ℤ), (-111848935901250 : ℤ), (8249874344500 : ℤ), (16235830071250 : ℤ)],
        ![(-55483943083625 : ℤ), (-19426540056625 : ℤ), (21661523928250 : ℤ), (-6631322747875 : ℤ)]],
      ![![(619291570498664 : ℤ), (-4996018065000 : ℤ), (-114245289633750 : ℤ), (-55483943083625 : ℤ)],
        ![(-4996018065000 : ℤ), (-117596982645125 : ℤ), (-111848935901250 : ℤ), (-19426540056625 : ℤ)],
        ![(-114245289633750 : ℤ), (-111848935901250 : ℤ), (8249874344500 : ℤ), (21661523928250 : ℤ)],
        ![(23497679214875 : ℤ), (43643231960375 : ℤ), (16235830071250 : ℤ), (-6631322747875 : ℤ)]],
      ![![(619291570498664 : ℤ), (-4996018065000 : ℤ), (-114245289633750 : ℤ), (23497679214875 : ℤ)],
        ![(-4996018065000 : ℤ), (-117596982645125 : ℤ), (-111848935901250 : ℤ), (43643231960375 : ℤ)],
        ![(-114245289633750 : ℤ), (-111848935901250 : ℤ), (8249874344500 : ℤ), (16235830071250 : ℤ)],
        ![(23497679214875 : ℤ), (43643231960375 : ℤ), (16235830071250 : ℤ), (3675777682375 : ℤ)]]],
    ![
      ![![(621560074627914 : ℤ), (-3083078275375 : ℤ), (-105055153516250 : ℤ), (-48648158519000 : ℤ)],
        ![(-3083078275375 : ℤ), (-105347525462125 : ℤ), (-105832425765375 : ℤ), (-22802667990375 : ℤ)],
        ![(-105055153516250 : ℤ), (-105832425765375 : ℤ), (-4147397572750 : ℤ), (13334989056625 : ℤ)],
        ![(-48648158519000 : ℤ), (-22802667990375 : ℤ), (13334989056625 : ℤ), (6755565410125 : ℤ)]],
      ![![(621560074627914 : ℤ), (-3083078275375 : ℤ), (-105055153516250 : ℤ), (18745671423000 : ℤ)],
        ![(-3083078275375 : ℤ), (-105347525462125 : ℤ), (-105832425765375 : ℤ), (36119236836125 : ℤ)],
        ![(-105055153516250 : ℤ), (-105832425765375 : ℤ), (-4147397572750 : ℤ), (20116325912125 : ℤ)],
        ![(-48648158519000 : ℤ), (-22802667990375 : ℤ), (13334989056625 : ℤ), (520585524625 : ℤ)]],
      ![![(621560074627914 : ℤ), (-3083078275375 : ℤ), (-105055153516250 : ℤ), (-48648158519000 : ℤ)],
        ![(-3083078275375 : ℤ), (-105347525462125 : ℤ), (-105832425765375 : ℤ), (-22802667990375 : ℤ)],
        ![(-105055153516250 : ℤ), (-105832425765375 : ℤ), (-4147397572750 : ℤ), (13334989056625 : ℤ)],
        ![(18745671423000 : ℤ), (36119236836125 : ℤ), (20116325912125 : ℤ), (520585524625 : ℤ)]],
      ![![(621560074627914 : ℤ), (-3083078275375 : ℤ), (-105055153516250 : ℤ), (18745671423000 : ℤ)],
        ![(-3083078275375 : ℤ), (-105347525462125 : ℤ), (-105832425765375 : ℤ), (36119236836125 : ℤ)],
        ![(-105055153516250 : ℤ), (-105832425765375 : ℤ), (-4147397572750 : ℤ), (20116325912125 : ℤ)],
        ![(18745671423000 : ℤ), (36119236836125 : ℤ), (20116325912125 : ℤ), (3206737537125 : ℤ)]]],
    ![
      ![![(624209125499414 : ℤ), (-1416557048500 : ℤ), (-97266144648875 : ℤ), (-43341488522625 : ℤ)],
        ![(-1416557048500 : ℤ), (-95413734761875 : ℤ), (-101716063491875 : ℤ), (-24829641342250 : ℤ)],
        ![(-97266144648875 : ℤ), (-101716063491875 : ℤ), (-17671956189000 : ℤ), (6275532577875 : ℤ)],
        ![(-43341488522625 : ℤ), (-24829641342250 : ℤ), (6275532577875 : ℤ), (4404472928875 : ℤ)]],
      ![![(624209125499414 : ℤ), (-1416557048500 : ℤ), (-97266144648875 : ℤ), (16054406207125 : ℤ)],
        ![(-1416557048500 : ℤ), (-95413734761875 : ℤ), (-101716063491875 : ℤ), (32477403887750 : ℤ)],
        ![(-97266144648875 : ℤ), (-101716063491875 : ℤ), (-17671956189000 : ℤ), (22614717083375 : ℤ)],
        ![(-43341488522625 : ℤ), (-24829641342250 : ℤ), (6275532577875 : ℤ), (2208917464125 : ℤ)]],
      ![![(624209125499414 : ℤ), (-1416557048500 : ℤ), (-97266144648875 : ℤ), (-43341488522625 : ℤ)],
        ![(-1416557048500 : ℤ), (-95413734761875 : ℤ), (-101716063491875 : ℤ), (-24829641342250 : ℤ)],
        ![(-97266144648875 : ℤ), (-101716063491875 : ℤ), (-17671956189000 : ℤ), (6275532577875 : ℤ)],
        ![(16054406207125 : ℤ), (32477403887750 : ℤ), (22614717083375 : ℤ), (2208917464125 : ℤ)]],
      ![![(624209125499414 : ℤ), (-1416557048500 : ℤ), (-97266144648875 : ℤ), (16054406207125 : ℤ)],
        ![(-1416557048500 : ℤ), (-95413734761875 : ℤ), (-101716063491875 : ℤ), (32477403887750 : ℤ)],
        ![(-97266144648875 : ℤ), (-101716063491875 : ℤ), (-17671956189000 : ℤ), (22614717083375 : ℤ)],
        ![(16054406207125 : ℤ), (32477403887750 : ℤ), (22614717083375 : ℤ), (2801305583375 : ℤ)]]],
    ![
      ![![(629814241229539 : ℤ), (-540370587375 : ℤ), (-94421098651250 : ℤ), (-40500876179875 : ℤ)],
        ![(-540370587375 : ℤ), (-90659773689000 : ℤ), (-98078907829500 : ℤ), (-24584279380250 : ℤ)],
        ![(-94421098651250 : ℤ), (-98078907829500 : ℤ), (-24850540094375 : ℤ), (2046929847625 : ℤ)],
        ![(-40500876179875 : ℤ), (-24584279380250 : ℤ), (2046929847625 : ℤ), (2662432005625 : ℤ)]],
      ![![(629814241229539 : ℤ), (-540370587375 : ℤ), (-94421098651250 : ℤ), (14837276306875 : ℤ)],
        ![(-540370587375 : ℤ), (-90659773689000 : ℤ), (-98078907829500 : ℤ), (30077037730750 : ℤ)],
        ![(-94421098651250 : ℤ), (-98078907829500 : ℤ), (-24850540094375 : ℤ), (24040279303875 : ℤ)],
        ![(-40500876179875 : ℤ), (-24584279380250 : ℤ), (2046929847625 : ℤ), (3004806529375 : ℤ)]],
      ![![(629814241229539 : ℤ), (-540370587375 : ℤ), (-94421098651250 : ℤ), (-40500876179875 : ℤ)],
        ![(-540370587375 : ℤ), (-90659773689000 : ℤ), (-98078907829500 : ℤ), (-24584279380250 : ℤ)],
        ![(-94421098651250 : ℤ), (-98078907829500 : ℤ), (-24850540094375 : ℤ), (2046929847625 : ℤ)],
        ![(14837276306875 : ℤ), (30077037730750 : ℤ), (24040279303875 : ℤ), (3004806529375 : ℤ)]],
      ![![(629814241229539 : ℤ), (-540370587375 : ℤ), (-94421098651250 : ℤ), (14837276306875 : ℤ)],
        ![(-540370587375 : ℤ), (-90659773689000 : ℤ), (-98078907829500 : ℤ), (30077037730750 : ℤ)],
        ![(-94421098651250 : ℤ), (-98078907829500 : ℤ), (-24850540094375 : ℤ), (24040279303875 : ℤ)],
        ![(14837276306875 : ℤ), (30077037730750 : ℤ), (24040279303875 : ℤ), (2238822727125 : ℤ)]]],
    ![
      ![![(633123044089289 : ℤ), (491304943625 : ℤ), (-88051960825375 : ℤ), (-36284085615750 : ℤ)],
        ![(491304943625 : ℤ), (-81458181235750 : ℤ), (-96648218489875 : ℤ), (-27113404767000 : ℤ)],
        ![(-88051960825375 : ℤ), (-96648218489875 : ℤ), (-39013613971625 : ℤ), (-4672887233250 : ℤ)],
        ![(-36284085615750 : ℤ), (-27113404767000 : ℤ), (-4672887233250 : ℤ), (472117386750 : ℤ)]],
      ![![(633123044089289 : ℤ), (491304943625 : ℤ), (-88051960825375 : ℤ), (13325501011000 : ℤ)],
        ![(491304943625 : ℤ), (-81458181235750 : ℤ), (-96648218489875 : ℤ), (28779354292500 : ℤ)],
        ![(-88051960825375 : ℤ), (-96648218489875 : ℤ), (-39013613971625 : ℤ), (27631471838000 : ℤ)],
        ![(-36284085615750 : ℤ), (-27113404767000 : ℤ), (-4672887233250 : ℤ), (4412468361250 : ℤ)]],
      ![![(633123044089289 : ℤ), (491304943625 : ℤ), (-88051960825375 : ℤ), (-36284085615750 : ℤ)],
        ![(491304943625 : ℤ), (-81458181235750 : ℤ), (-96648218489875 : ℤ), (-27113404767000 : ℤ)],
        ![(-88051960825375 : ℤ), (-96648218489875 : ℤ), (-39013613971625 : ℤ), (-4672887233250 : ℤ)],
        ![(13325501011000 : ℤ), (28779354292500 : ℤ), (27631471838000 : ℤ), (4412468361250 : ℤ)]],
      ![![(633123044089289 : ℤ), (491304943625 : ℤ), (-88051960825375 : ℤ), (13325501011000 : ℤ)],
        ![(491304943625 : ℤ), (-81458181235750 : ℤ), (-96648218489875 : ℤ), (28779354292500 : ℤ)],
        ![(-88051960825375 : ℤ), (-96648218489875 : ℤ), (-39013613971625 : ℤ), (27631471838000 : ℤ)],
        ![(13325501011000 : ℤ), (28779354292500 : ℤ), (27631471838000 : ℤ), (472117386750 : ℤ)]]]]

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
                  Certificate.inside)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (-816 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-720 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside))
                  Certificate.inside))
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-960 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (-864 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-720 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside))
                Certificate.inside))
            Certificate.inside)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.splitY (-720 : ℤ)
                          (Certificate.splitX (-744 : ℤ)
                            (Certificate.splitY (-744 : ℤ)
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
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.inside
              Certificate.inside)
            (Certificate.splitY (384 : ℤ)
              Certificate.inside
              Certificate.inside))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-432 : ℤ)
                        Certificate.inside
                        Certificate.inside)))
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    Certificate.inside)))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-412508154193628259 : ℤ) (6305039478318694400 : ℕ) none)
                            (Certificate.cross (-31634013364043493 : ℤ) (225179981368524800 : ℕ) none)))
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (-278264973462543148983 : ℤ) (3228180212899171532800 : ℕ) none)
                            (Certificate.cross (-25482784514880424947 : ℤ) (158526706883441459200 : ℕ) none))
                          (Certificate.cross (-142612020258201381 : ℤ) (731834939447705600 : ℕ) none))))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-28218304592106165447 : ℤ) (158526706883441459200 : ℕ) none))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-66344625623617131 : ℤ) (309622474381721600 : ℕ) none)
                          (Certificate.cross (-24176538555806157 : ℤ) (91479367430963200 : ℕ) none)))
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.cross (-2263546511619925173 : ℤ) (9232379236109516800 : ℕ) none)
                        Certificate.outside)))))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.cross (-620718770303405673 : ℤ) (5854679515581644800 : ℕ) none))
                      (Certificate.cross (-201709074461762631 : ℤ) (1576259869579673600 : ℕ) none)))
                  (Certificate.cross (-7875587345217879 : ℤ) (51017339528806400 : ℕ) none))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.cross (-2519835672225813267 : ℤ) (14411518807585587200 : ℕ) none)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-168 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-156 : ℤ)
                                Certificate.outside
                                Certificate.outside))))
                        Certificate.outside))
                    Certificate.outside))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            Certificate.inside
            Certificate.inside)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        Certificate.inside))))
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-66344625623617131 : ℤ) (309622474381721600 : ℕ) none))
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-28218304592106165447 : ℤ) (158526706883441459200 : ℕ) none)
                          (Certificate.cross (-24176538555806157 : ℤ) (91479367430963200 : ℕ) none))))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.cross (-28287482813263296201 : ℤ) (403522526612396441600 : ℕ) none)
                            (Certificate.cross (-25482784514880424947 : ℤ) (158526706883441459200 : ℕ) none)))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (360 : ℤ)
                            (Certificate.cross (-290218656451461298233 : ℤ) (3228180212899171532800 : ℕ) none)
                            (Certificate.splitY (-168 : ℤ)
                              (Certificate.cross (-412508154193628259 : ℤ) (6305039478318694400 : ℕ) none)
                              (Certificate.cross (-31634013364043493 : ℤ) (225179981368524800 : ℕ) none)))
                          (Certificate.cross (-142612020258201381 : ℤ) (731834939447705600 : ℕ) none)))
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.cross (-330542890486942881 : ℤ) (1154047404513689600 : ℕ) none)
                        Certificate.outside))))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.cross (-1524469600817917509 : ℤ) (19815838360430182400 : ℕ) none)
                        (Certificate.cross (-620718770303405673 : ℤ) (5854679515581644800 : ℕ) none)))
                    (Certificate.cross (-201709074461762631 : ℤ) (1576259869579673600 : ℕ) none))
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.cross (-124731509149388203197 : ℤ) (590872271111009075200 : ℕ) none)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.cross (-16154803871968629 : ℤ) (51017339528806400 : ℕ) none)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
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
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (1392 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (1512 : ℤ)
                            (Certificate.splitY (-168 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-168 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-156 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))))
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
                      Certificate.inside
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (24 : ℤ)
                            (Certificate.cross (-6407839567882658697 : ℤ) (50440315826549555200 : ℕ) none)
                            (Certificate.cross (-5373912288540108009 : ℤ) (19815838360430182400 : ℕ) none)))
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (72 : ℤ)
                            (Certificate.cross (-724676323778175292233 : ℤ) (3228180212899171532800 : ℕ) none)
                            (Certificate.splitY (120 : ℤ)
                              (Certificate.cross (-100434942392603548701 : ℤ) (403522526612396441600 : ℕ) none)
                              (Certificate.cross (-49447445951180569947 : ℤ) (158526706883441459200 : ℕ) none)))
                          (Certificate.cross (-2061609523001027673 : ℤ) (5854679515581644800 : ℕ) none))))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.cross (-100434942392603548701 : ℤ) (403522526612396441600 : ℕ) none)
                            (Certificate.splitY (72 : ℤ)
                              (Certificate.cross (-724676323778175292233 : ℤ) (3228180212899171532800 : ℕ) none)
                              (Certificate.cross (-49447445951180569947 : ℤ) (158526706883441459200 : ℕ) none))))
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-582909956574037042983 : ℤ) (3228180212899171532800 : ℕ) none)
                            (Certificate.cross (-5373912288540108009 : ℤ) (19815838360430182400 : ℕ) none))
                          (Certificate.cross (-2061609523001027673 : ℤ) (5854679515581644800 : ℕ) none)))
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.cross (-5866696282590120001983 : ℤ) (17063238268181335244800 : ℕ) none)
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside)))
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (-1003252802894716881 : ℤ) (2420684799711641600 : ℕ) none)
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-39935004287779805259 : ℤ) (100880631653099110400 : ℕ) none)
                      Certificate.outside)
                    Certificate.outside)
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
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (432 : ℤ)
                          (Certificate.splitX (360 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (408 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside))
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
                          (Certificate.splitX (408 : ℤ)
                            (Certificate.splitY (360 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside))
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              Certificate.outside))
          Certificate.outside)
        (Certificate.splitY (768 : ℤ)
          Certificate.outside
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
                  Certificate.inside)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (-816 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-720 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside))
                  Certificate.inside))
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-960 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (-864 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-720 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside))
                Certificate.inside))
            Certificate.inside)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.splitY (-720 : ℤ)
                          (Certificate.splitX (-744 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside)
              Certificate.inside)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            Certificate.inside
            (Certificate.splitY (384 : ℤ)
              Certificate.inside
              Certificate.inside))
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (864 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (912 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (936 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (924 : ℤ)
                                  Certificate.inside
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside))
                        Certificate.inside))
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    Certificate.inside)))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-168 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-189382295550126673 : ℤ) (1576259869579673600 : ℕ) none)))
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.cross (-12851446484834311447 : ℤ) (100880631653099110400 : ℕ) none)
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (-4133174372879006759 : ℤ) (26120877838748876800 : ℕ) none)
                            (Certificate.cross (-10463035112071921 : ℤ) (56294995342131200 : ℕ) none)))))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.cross (-13307228400276377947 : ℤ) (100880631653099110400 : ℕ) none)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-583226432011201 : ℤ) (3518437208883200 : ℕ) none)
                          (Certificate.cross (-2427777074867879 : ℤ) (9675702324428800 : ℕ) none)))
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.cross (-1992562318365389923 : ℤ) (8331659310635417600 : ℕ) none)
                        Certificate.outside)))))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (432 : ℤ)
                          (Certificate.cross (-817658635713213509 : ℤ) (12610078956637388800 : ℕ) none)
                          (Certificate.cross (-517566562211196673 : ℤ) (4953959590107545600 : ℕ) none)))
                      (Certificate.cross (-183779287208085131 : ℤ) (1463669878895411200 : ℕ) none)))
                  (Certificate.cross (-7350586470354629 : ℤ) (49258120924364800 : ℕ) none))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-1656923539500064838983 : ℤ) (13373889453439424921600 : ℕ) none)
                            (Certificate.cross (-393439537583291035451 : ℤ) (2536427310135063347200 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-132 : ℤ)
                                Certificate.outside
                                Certificate.outside))
                            Certificate.outside))))
                    Certificate.outside))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            Certificate.inside
            Certificate.inside)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      Certificate.inside)))
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.cross (-583226432011201 : ℤ) (3518437208883200 : ℕ) none)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-13307228400276377947 : ℤ) (100880631653099110400 : ℕ) none)
                          (Certificate.cross (-2427777074867879 : ℤ) (9675702324428800 : ℕ) none))))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-12851446484834311447 : ℤ) (100880631653099110400 : ℕ) none))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (360 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-189382295550126673 : ℤ) (1576259869579673600 : ℕ) none))
                          (Certificate.splitX (360 : ℤ)
                            (Certificate.cross (-282266554823696609951 : ℤ) (1671736181679928115200 : ℕ) none)
                            (Certificate.cross (-10463035112071921 : ℤ) (56294995342131200 : ℕ) none))))
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-542368885904626127951 : ℤ) (2536427310135063347200 : ℕ) none)
                          Certificate.outside)
                        Certificate.outside))))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.cross (-817658635713213509 : ℤ) (12610078956637388800 : ℕ) none)
                        (Certificate.cross (-517566562211196673 : ℤ) (4953959590107545600 : ℕ) none)))
                    (Certificate.cross (-183779287208085131 : ℤ) (1463669878895411200 : ℕ) none))
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (408 : ℤ)
                            (Certificate.cross (-1930076451812180518483 : ℤ) (13373889453439424921600 : ℕ) none)
                            (Certificate.cross (-393439537583291035451 : ℤ) (2536427310135063347200 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.cross (-803286166916021 : ℤ) (2418925581107200 : ℕ) none)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (864 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (912 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (936 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (924 : ℤ)
                                Certificate.inside
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside))
                      Certificate.inside))
                  Certificate.inside)
                Certificate.inside)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
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
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (1392 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            (Certificate.splitY (-120 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-120 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-132 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside))))
                      Certificate.outside)))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-2955046227551978759 : ℤ) (12610078956637388800 : ℕ) none))
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (72 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-28853669001949620697 : ℤ) (100880631653099110400 : ℕ) none))
                          (Certificate.splitX (72 : ℤ)
                            (Certificate.cross (-62998113793716401197 : ℤ) (208967022709991014400 : ℕ) none)
                            (Certificate.cross (-1673564503442335423 : ℤ) (4953959590107545600 : ℕ) none)))))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (120 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-28853669001949620697 : ℤ) (100880631653099110400 : ℕ) none)))
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.cross (-2955046227551978759 : ℤ) (12610078956637388800 : ℕ) none)
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-532818839300949096701 : ℤ) (1671736181679928115200 : ℕ) none)
                            (Certificate.cross (-1673564503442335423 : ℤ) (4953959590107545600 : ℕ) none))))
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.splitY (120 : ℤ)
                              (Certificate.cross (-15148305653107164343739 : ℤ) (51650883406386744524800 : ℕ) none)
                              (Certificate.cross (-4384521511154711568733 : ℤ) (13373889453439424921600 : ℕ) none))
                            (Certificate.cross (-894094058886160645451 : ℤ) (2536427310135063347200 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)))
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.cross (-173377929638572254697 : ℤ) (533226195880666726400 : ℕ) none)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.cross (-757936735815075296951 : ℤ) (2536427310135063347200 : ℕ) none)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (432 : ℤ)
                          (Certificate.splitX (360 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (408 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside))
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
                          (Certificate.splitX (408 : ℤ)
                            (Certificate.splitY (360 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (360 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside)
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
              Certificate.outside)
            Certificate.outside))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside)
              Certificate.outside)
            Certificate.outside)
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
                  Certificate.inside)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (-864 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-672 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside))
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-960 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-672 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside))
            Certificate.inside)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.splitY (-720 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-720 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside)
              Certificate.inside)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (1152 : ℤ)
              Certificate.inside
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (1392 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (1368 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside))
                (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
            (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-432 : ℤ)
                        Certificate.inside
                        Certificate.inside)))
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    Certificate.inside)))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.cross (-10225324875597391 : ℤ) (225179981368524800 : ℕ) none)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.cross (-9237308596077959 : ℤ) (56294995342131200 : ℕ) none))))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.cross (-1557848991374323 : ℤ) (7036874417766400 : ℕ) none))
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.cross (-545977162977278141 : ℤ) (2476979795053772800 : ℕ) none)
                        Certificate.outside)))))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (432 : ℤ)
                          (Certificate.cross (-22529906750552003 : ℤ) (1801439850948198400 : ℕ) none)
                          (Certificate.cross (-43929047488268797 : ℤ) (450359962737049600 : ℕ) none)))
                      (Certificate.cross (-52549133440885877 : ℤ) (450359962737049600 : ℕ) none)))
                  (Certificate.cross (-701890537959181 : ℤ) (5277655813324800 : ℕ) none))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-52106268362107887023 : ℤ) (461168601842738790400 : ℕ) none)
                            (Certificate.cross (-33152941225035958439 : ℤ) (230584300921369395200 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (960 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          (Certificate.splitX (-120 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          (Certificate.splitX (-120 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              (Certificate.splitX (-108 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              (Certificate.splitX (-108 : ℤ)
                                Certificate.outside
                                Certificate.outside))))))
                    Certificate.outside))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        Certificate.inside))))
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)))
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.cross (-1557848991374323 : ℤ) (7036874417766400 : ℕ) none))))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-10225324875597391 : ℤ) (225179981368524800 : ℕ) none)
                          (Certificate.cross (-9237308596077959 : ℤ) (56294995342131200 : ℕ) none)))
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-42540352288330076939 : ℤ) (230584300921369395200 : ℕ) none)
                          Certificate.outside)
                        Certificate.outside))))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.cross (-22529906750552003 : ℤ) (1801439850948198400 : ℕ) none)
                        (Certificate.cross (-43929047488268797 : ℤ) (450359962737049600 : ℕ) none)))
                    (Certificate.cross (-52549133440885877 : ℤ) (450359962737049600 : ℕ) none))
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (408 : ℤ)
                            (Certificate.splitY (-168 : ℤ)
                              (Certificate.cross (-389223027729758668913 : ℤ) (7378697629483820646400 : ℕ) none)
                              (Certificate.cross (-408941100860702305661 : ℤ) (3228180212899171532800 : ℕ) none))
                            (Certificate.cross (-33152941225035958439 : ℤ) (230584300921369395200 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.cross (-1335346317776969 : ℤ) (4068193022771200 : ℕ) none)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (1344 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (1392 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (1368 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (960 : ℤ)
                Certificate.outside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1056 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (1392 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1464 : ℤ)
                            (Certificate.splitY (-120 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-120 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            (Certificate.splitY (-120 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1500 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-108 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)))
                            (Certificate.splitY (-120 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                (Certificate.splitY (-108 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-108 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))))))
                      Certificate.outside)))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.cross (-187684434865152503 : ℤ) (1801439850948198400 : ℕ) none)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (-3181512194879094649 : ℤ) (14411518807585587200 : ℕ) none)
                          (Certificate.splitX (72 : ℤ)
                            (Certificate.cross (-13885227511669857149 : ℤ) (50440315826549555200 : ℕ) none)
                            (Certificate.cross (-145017587093669797 : ℤ) (450359962737049600 : ℕ) none)))))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-3181512194879094649 : ℤ) (14411518807585587200 : ℕ) none))
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.cross (-187684434865152503 : ℤ) (1801439850948198400 : ℕ) none)
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-17204928196212150331 : ℤ) (57646075230342348800 : ℕ) none)
                            (Certificate.cross (-145017587093669797 : ℤ) (450359962737049600 : ℕ) none))))
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.splitY (120 : ℤ)
                              (Certificate.cross (-1751342995733800507163 : ℤ) (7378697629483820646400 : ℕ) none)
                              (Certificate.cross (-1003262470820717665661 : ℤ) (3228180212899171532800 : ℕ) none))
                            (Certificate.cross (-78300256574636709689 : ℤ) (230584300921369395200 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)))
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.cross (-48778641239824432649 : ℤ) (158526706883441459200 : ℕ) none)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.cross (-63616402135259924189 : ℤ) (230584300921369395200 : ℕ) none)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (432 : ℤ)
                          (Certificate.splitX (360 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside))
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
                          (Certificate.splitX (408 : ℤ)
                            Certificate.outside
                            Certificate.outside))
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          (Certificate.splitX (408 : ℤ)
                            (Certificate.splitY (408 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)
                          Certificate.outside)
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
              Certificate.outside)
            Certificate.outside))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside)
              Certificate.outside)
            Certificate.outside)
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
                  Certificate.inside)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (-816 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-720 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside))
                  Certificate.inside))
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-960 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (-864 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-720 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside))
                Certificate.inside))
            Certificate.inside)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.splitY (-720 : ℤ)
                          (Certificate.splitX (-744 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          Certificate.inside
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-432 : ℤ)
                        Certificate.inside
                        Certificate.inside)))
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    Certificate.inside)))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-8399161230364483 : ℤ) (56294995342131200 : ℕ) none))))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-9689836157758157 : ℤ) (49258120924364800 : ℕ) none))
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.cross (-1388463837814290173 : ℤ) (6530219459687219200 : ℕ) none)
                        (Certificate.cross (-664990343753063 : ℤ) (2418925581107200 : ℕ) none))))))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (432 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-285467620227269423 : ℤ) (3152519739159347200 : ℕ) none)))
                      (Certificate.cross (-137972666774278381 : ℤ) (1238489897526886400 : ℕ) none)))
                  (Certificate.cross (-5535721415527879 : ℤ) (45739683715481600 : ℕ) none))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-599348594732945136233 : ℤ) (5995191823955604275200 : ℕ) none)
                            (Certificate.cross (-32035565890472038243 : ℤ) (230584300921369395200 : ℕ) none))
                          (Certificate.cross (-66486659158559485697 : ℤ) (417934045419982028800 : ℕ) none))
                        (Certificate.cross (-16303738226852463259 : ℤ) (79263353441720729600 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (960 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1248 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-48 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (1392 : ℤ)
                          (Certificate.splitX (-72 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.splitY (1416 : ℤ)
                              (Certificate.splitX (-84 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              (Certificate.splitX (-84 : ℤ)
                                Certificate.outside
                                Certificate.outside))
                            Certificate.outside))
                        Certificate.outside)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (1488 : ℤ)
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.splitY (1464 : ℤ)
                              (Certificate.splitX (-84 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              (Certificate.splitX (-84 : ℤ)
                                Certificate.outside
                                Certificate.outside))
                            Certificate.outside)
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              (Certificate.splitX (-84 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              (Certificate.splitX (-84 : ℤ)
                                Certificate.outside
                                Certificate.outside))
                            Certificate.outside))
                        Certificate.outside))))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        Certificate.inside))))
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)))
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-9689836157758157 : ℤ) (49258120924364800 : ℕ) none))))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-8399161230364483 : ℤ) (56294995342131200 : ℕ) none)))
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-259138687597384087201 : ℤ) (1614090106449585766400 : ℕ) none)
                          (Certificate.cross (-203812970092034881 : ℤ) (816277432460902400 : ℕ) none))
                        (Certificate.cross (-664990343753063 : ℤ) (2418925581107200 : ℕ) none)))))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (432 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-285467620227269423 : ℤ) (3152519739159347200 : ℕ) none)))
                    (Certificate.cross (-137972666774278381 : ℤ) (1238489897526886400 : ℕ) none))
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (408 : ℤ)
                            (Certificate.cross (-640371855271573900733 : ℤ) (5995191823955604275200 : ℕ) none)
                            (Certificate.cross (-32035565890472038243 : ℤ) (230584300921369395200 : ℕ) none))
                          (Certificate.cross (-78281691314662583447 : ℤ) (417934045419982028800 : ℕ) none))
                        (Certificate.cross (-16303738226852463259 : ℤ) (79263353441720729600 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.cross (-658261972887797 : ℤ) (1979120929996800 : ℕ) none)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (960 : ℤ)
                Certificate.outside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1056 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1296 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.outside
                          Certificate.outside)))))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1392 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (1368 : ℤ)
                            (Certificate.splitY (-72 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-72 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (1416 : ℤ)
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.splitX (1404 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-84 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside)
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.splitX (1428 : ℤ)
                                (Certificate.splitY (-84 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-84 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside))
                          Certificate.outside)))
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (1464 : ℤ)
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.splitX (1452 : ℤ)
                                (Certificate.splitY (-84 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-84 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside)
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.splitX (1476 : ℤ)
                                (Certificate.splitY (-84 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-84 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside))
                          Certificate.outside)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (1512 : ℤ)
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.splitX (1500 : ℤ)
                                (Certificate.splitY (-84 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-84 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside)
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                (Certificate.splitY (-84 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                Certificate.outside)
                              Certificate.outside))
                          Certificate.outside)))))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (48 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (72 : ℤ)
                            (Certificate.cross (-22774278493114530197 : ℤ) (93674872249306316800 : ℕ) none)
                            (Certificate.cross (-991460895910988423 : ℤ) (3152519739159347200 : ℕ) none)))))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (48 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-208173548254427960701 : ℤ) (749398977994450534400 : ℕ) none)
                            (Certificate.cross (-991460895910988423 : ℤ) (3152519739159347200 : ℕ) none))))
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.cross (-1776596389009192810733 : ℤ) (5995191823955604275200 : ℕ) none)
                            (Certificate.splitY (120 : ℤ)
                              (Certificate.cross (-1776596389009192810733 : ℤ) (5995191823955604275200 : ℕ) none)
                              (Certificate.cross (-541958792225129031451 : ℤ) (1614090106449585766400 : ℕ) none)))
                          (Certificate.cross (-19602911554404353509 : ℤ) (52241755677497753600 : ℕ) none))
                        (Certificate.cross (-512936551633895131 : ℤ) (1238489897526886400 : ℕ) none))))
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-418626792154335562951 : ℤ) (1614090106449585766400 : ℕ) none)
                          (Certificate.cross (-125732277204546718697 : ℤ) (417934045419982028800 : ℕ) none))
                        (Certificate.cross (-29341649366057443009 : ℤ) (79263353441720729600 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.cross (-418626792154335562951 : ℤ) (1614090106449585766400 : ℕ) none)
                          (Certificate.cross (-145396944074545838447 : ℤ) (417934045419982028800 : ℕ) none))
                        (Certificate.cross (-29341649366057443009 : ℤ) (79263353441720729600 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside))
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    Certificate.outside))))
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
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)))
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          (Certificate.splitX (408 : ℤ)
                            (Certificate.splitY (408 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)
                          Certificate.outside)
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
              Certificate.outside)
            Certificate.outside))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside)
              Certificate.outside)
            Certificate.outside)
          Certificate.outside))],
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                Certificate.inside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (-864 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-672 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside))
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-960 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-672 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside))
            Certificate.inside)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-432 : ℤ)
                        Certificate.inside
                        Certificate.inside)))
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    Certificate.inside)))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-13213465078668003 : ℤ) (140737488355328000 : ℕ) none))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.cross (-68380732300563 : ℤ) (549755813888000 : ℕ) none)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.cross (-510869251771087899 : ℤ) (2814749767106560000 : ℕ) none)
                        (Certificate.cross (-276156633312969 : ℤ) (1099511627776000 : ℕ) none))))))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (432 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-89126434651945149 : ℤ) (1125899906842624000 : ℕ) none)))
                      (Certificate.cross (-56111081588203503 : ℤ) (562949953421312000 : ℕ) none)))
                  (Certificate.cross (-7252379463893383 : ℤ) (70368744177664000 : ℕ) none))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-42645637036848572679 : ℤ) (1152921504606846976000 : ℕ) none)
                            (Certificate.cross (-65880541660412753163 : ℤ) (576460752303423488000 : ℕ) none))
                          (Certificate.cross (-26309178941160574911 : ℤ) (180143985094819840000 : ℕ) none))
                        (Certificate.cross (-6773220382934890317 : ℤ) (36028797018963968000 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (960 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1248 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-48 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (1392 : ℤ)
                          (Certificate.splitX (-72 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          (Certificate.splitX (-72 : ℤ)
                            Certificate.outside
                            Certificate.outside))
                        Certificate.outside)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (1488 : ℤ)
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.splitY (1464 : ℤ)
                              (Certificate.splitX (-84 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              (Certificate.splitX (-84 : ℤ)
                                Certificate.outside
                                Certificate.outside))
                            Certificate.outside)
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              (Certificate.splitX (-84 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              (Certificate.splitX (-84 : ℤ)
                                Certificate.outside
                                Certificate.outside))
                            Certificate.outside))
                        Certificate.outside))))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        Certificate.inside))))
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)))
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-68380732300563 : ℤ) (549755813888000 : ℕ) none))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.cross (-13213465078668003 : ℤ) (140737488355328000 : ℕ) none)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.cross (-19221717554945907 : ℤ) (87960930222080000 : ℕ) none)
                        (Certificate.cross (-276156633312969 : ℤ) (1099511627776000 : ℕ) none)))))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (432 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-89126434651945149 : ℤ) (1125899906842624000 : ℕ) none)))
                    (Certificate.cross (-56111081588203503 : ℤ) (562949953421312000 : ℕ) none))
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (408 : ℤ)
                            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                            (Certificate.cross (-65880541660412753163 : ℤ) (576460752303423488000 : ℕ) none))
                          (Certificate.cross (-29526982607778286161 : ℤ) (180143985094819840000 : ℕ) none))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-26309178941160574911 : ℤ) (180143985094819840000 : ℕ) none)
                          Certificate.outside))
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.cross (-1223319967685219 : ℤ) (3848290697216000 : ℕ) none)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (960 : ℤ)
                Certificate.outside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1056 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1296 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.outside
                          Certificate.outside)))))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1392 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (1368 : ℤ)
                            (Certificate.splitY (-72 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-72 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (1416 : ℤ)
                            (Certificate.splitY (-72 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-72 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)))
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (1464 : ℤ)
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.splitX (1452 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-84 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside)
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.splitX (1476 : ℤ)
                                (Certificate.splitY (-84 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-84 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside))
                          Certificate.outside)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (1512 : ℤ)
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.splitX (1500 : ℤ)
                                (Certificate.splitY (-84 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-84 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside)
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                (Certificate.splitY (-84 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                Certificate.outside)
                              Certificate.outside))
                          Certificate.outside)))))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (48 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (72 : ℤ)
                            (Certificate.cross (-1549057504183485411 : ℤ) (18014398509481984000 : ℕ) none)
                            (Certificate.cross (-329036487366068649 : ℤ) (1125899906842624000 : ℕ) none)))))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (48 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-26159457139911729663 : ℤ) (144115188075855872000 : ℕ) none)
                            (Certificate.cross (-329036487366068649 : ℤ) (1125899906842624000 : ℕ) none))))
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.cross (-268557435730461518679 : ℤ) (1152921504606846976000 : ℕ) none)
                            (Certificate.splitY (120 : ℤ)
                              (Certificate.cross (-268557435730461518679 : ℤ) (1152921504606846976000 : ℕ) none)
                              (Certificate.cross (-186646603275011084913 : ℤ) (576460752303423488000 : ℕ) none)))
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.cross (-42665964740317388661 : ℤ) (126100789566373888000 : ℕ) none)
                            Certificate.outside))
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-402603858703474255347 : ℤ) (1152921504606846976000 : ℕ) none)
                            Certificate.outside)
                          Certificate.outside))))
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.cross (-49938023700077469411 : ℤ) (180143985094819840000 : ℕ) none)
                        (Certificate.cross (-12848470791533144067 : ℤ) (36028797018963968000 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.cross (-122029105621767031413 : ℤ) (576460752303423488000 : ℕ) none)
                          (Certificate.cross (-60098484712923260661 : ℤ) (180143985094819840000 : ℕ) none))
                        (Certificate.cross (-12848470791533144067 : ℤ) (36028797018963968000 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside))
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
                        Certificate.outside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          (Certificate.splitX (408 : ℤ)
                            (Certificate.splitY (408 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (408 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)
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
              Certificate.outside)
            Certificate.outside))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside)
              Certificate.outside)
            Certificate.outside)
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

end BerryEsseen.N2NeededIntegerPointwise12

#print axioms BerryEsseen.N2NeededIntegerPointwise12.powers_entries
#print axioms BerryEsseen.N2NeededIntegerPointwise12.powers_eq
#print axioms BerryEsseen.N2NeededIntegerPointwise12.checks
#print axioms BerryEsseen.N2NeededIntegerPointwise12.pointwise
