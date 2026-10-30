module

public import BerryEsseen.N2NeededIntegerData
public import BerryEsseen.N2IntegerPointwiseReplay

@[expose] public section

/-! 2026-10-29: integer power numerators and the unchanged original
rows010..014 closed trees. The entries equality is the semantic cache bridge.
No Bernstein coefficient or host closed flag is a premise. -/

namespace BerryEsseen.N2NeededIntegerPointwise01

open N2NeededData N2NeededIntegerData N2IntegerBernstein
  N2IntegerRectangleCertificate N2MajorantPolynomials

def rowIndex (j : Fin 5) : Fin 65 :=
  ⟨1 * 5 + j.val,
    lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (1 * 5)) (by decide)⟩

def signX : Fin 4 → ℚ := N2IntegerPointwiseReplay.signX
def signY : Fin 4 → ℚ := N2IntegerPointwiseReplay.signY

def powers : Fin 5 → Fin 4 → IntPower :=
  ![
    ![
      ![![(16965841391414 : ℤ), (-49279676977000 : ℤ), (49130851083375 : ℤ), (-51021090776500 : ℤ)],
        ![(-49279676977000 : ℤ), (140126917934500 : ℤ), (-139669088649125 : ℤ), (-26189696830000 : ℤ)],
        ![(49130851083375 : ℤ), (-139669088649125 : ℤ), (45357692516250 : ℤ), (109530308168625 : ℤ)],
        ![(-51021090776500 : ℤ), (-26189696830000 : ℤ), (109530308168625 : ℤ), (66958454942375 : ℤ)]],
      ![![(16965841391414 : ℤ), (-49279676977000 : ℤ), (49130851083375 : ℤ), (4443884457250 : ℤ)],
        ![(-49279676977000 : ℤ), (140126917934500 : ℤ), (-139669088649125 : ℤ), (50628880969000 : ℤ)],
        ![(49130851083375 : ℤ), (-139669088649125 : ℤ), (45357692516250 : ℤ), (-17041920301125 : ℤ)],
        ![(-51021090776500 : ℤ), (-26189696830000 : ℤ), (109530308168625 : ℤ), (-76945062570125 : ℤ)]],
      ![![(16965841391414 : ℤ), (-49279676977000 : ℤ), (49130851083375 : ℤ), (-51021090776500 : ℤ)],
        ![(-49279676977000 : ℤ), (140126917934500 : ℤ), (-139669088649125 : ℤ), (-26189696830000 : ℤ)],
        ![(49130851083375 : ℤ), (-139669088649125 : ℤ), (45357692516250 : ℤ), (109530308168625 : ℤ)],
        ![(4443884457250 : ℤ), (50628880969000 : ℤ), (-17041920301125 : ℤ), (-76945062570125 : ℤ)]],
      ![![(16965841391414 : ℤ), (-49279676977000 : ℤ), (49130851083375 : ℤ), (4443884457250 : ℤ)],
        ![(-49279676977000 : ℤ), (140126917934500 : ℤ), (-139669088649125 : ℤ), (50628880969000 : ℤ)],
        ![(49130851083375 : ℤ), (-139669088649125 : ℤ), (45357692516250 : ℤ), (-17041920301125 : ℤ)],
        ![(4443884457250 : ℤ), (50628880969000 : ℤ), (-17041920301125 : ℤ), (2772954434875 : ℤ)]]],
    ![
      ![![(26428342143289 : ℤ), (-62106892850875 : ℤ), (49745937446875 : ℤ), (-50215338982625 : ℤ)],
        ![(-62106892850875 : ℤ), (150729139185000 : ℤ), (-132607986916750 : ℤ), (-28788205134250 : ℤ)],
        ![(49745937446875 : ℤ), (-132607986916750 : ℤ), (47264156466875 : ℤ), (115575733556375 : ℤ)],
        ![(-50215338982625 : ℤ), (-28788205134250 : ℤ), (115575733556375 : ℤ), (74702053277625 : ℤ)]],
      ![![(26428342143289 : ℤ), (-62106892850875 : ℤ), (49745937446875 : ℤ), (3840265072375 : ℤ)],
        ![(-62106892850875 : ℤ), (150729139185000 : ℤ), (-132607986916750 : ℤ), (47211486187000 : ℤ)],
        ![(49745937446875 : ℤ), (-132607986916750 : ℤ), (47264156466875 : ℤ), (-19595224271625 : ℤ)],
        ![(-50215338982625 : ℤ), (-28788205134250 : ℤ), (115575733556375 : ℤ), (-80616723207625 : ℤ)]],
      ![![(26428342143289 : ℤ), (-62106892850875 : ℤ), (49745937446875 : ℤ), (-50215338982625 : ℤ)],
        ![(-62106892850875 : ℤ), (150729139185000 : ℤ), (-132607986916750 : ℤ), (-28788205134250 : ℤ)],
        ![(49745937446875 : ℤ), (-132607986916750 : ℤ), (47264156466875 : ℤ), (115575733556375 : ℤ)],
        ![(3840265072375 : ℤ), (47211486187000 : ℤ), (-19595224271625 : ℤ), (-80616723207625 : ℤ)]],
      ![![(26428342143289 : ℤ), (-62106892850875 : ℤ), (49745937446875 : ℤ), (3840265072375 : ℤ)],
        ![(-62106892850875 : ℤ), (150729139185000 : ℤ), (-132607986916750 : ℤ), (47211486187000 : ℤ)],
        ![(49745937446875 : ℤ), (-132607986916750 : ℤ), (47264156466875 : ℤ), (-19595224271625 : ℤ)],
        ![(3840265072375 : ℤ), (47211486187000 : ℤ), (-19595224271625 : ℤ), (4255410093125 : ℤ)]]],
    ![
      ![![(44064659469914 : ℤ), (-61280416272000 : ℤ), (34356091310875 : ℤ), (-59051276223250 : ℤ)],
        ![(-61280416272000 : ℤ), (160822233025500 : ℤ), (-139174063040625 : ℤ), (-30089405927250 : ℤ)],
        ![(34356091310875 : ℤ), (-139174063040625 : ℤ), (60042858697250 : ℤ), (120130717011000 : ℤ)],
        ![(-59051276223250 : ℤ), (-30089405927250 : ℤ), (120130717011000 : ℤ), (74310185828500 : ℤ)]],
      ![![(44064659469914 : ℤ), (-61280416272000 : ℤ), (34356091310875 : ℤ), (3544558914250 : ℤ)],
        ![(-61280416272000 : ℤ), (160822233025500 : ℤ), (-139174063040625 : ℤ), (44552134114250 : ℤ)],
        ![(34356091310875 : ℤ), (-139174063040625 : ℤ), (60042858697250 : ℤ), (-14233950822500 : ℤ)],
        ![(-59051276223250 : ℤ), (-30089405927250 : ℤ), (120130717011000 : ℤ), (-77806382228250 : ℤ)]],
      ![![(44064659469914 : ℤ), (-61280416272000 : ℤ), (34356091310875 : ℤ), (-59051276223250 : ℤ)],
        ![(-61280416272000 : ℤ), (160822233025500 : ℤ), (-139174063040625 : ℤ), (-30089405927250 : ℤ)],
        ![(34356091310875 : ℤ), (-139174063040625 : ℤ), (60042858697250 : ℤ), (120130717011000 : ℤ)],
        ![(3544558914250 : ℤ), (44552134114250 : ℤ), (-14233950822500 : ℤ), (-77806382228250 : ℤ)]],
      ![![(44064659469914 : ℤ), (-61280416272000 : ℤ), (34356091310875 : ℤ), (3544558914250 : ℤ)],
        ![(-61280416272000 : ℤ), (160822233025500 : ℤ), (-139174063040625 : ℤ), (44552134114250 : ℤ)],
        ![(34356091310875 : ℤ), (-139174063040625 : ℤ), (60042858697250 : ℤ), (-14233950822500 : ℤ)],
        ![(3544558914250 : ℤ), (44552134114250 : ℤ), (-14233950822500 : ℤ), (1695245694500 : ℤ)]]],
    ![
      ![![(26711236103289 : ℤ), (-70692733739875 : ℤ), (63451720541250 : ℤ), (-58102023436125 : ℤ)],
        ![(-70692733739875 : ℤ), (164926663710750 : ℤ), (-129468008513750 : ℤ), (-20272736769625 : ℤ)],
        ![(63451720541250 : ℤ), (-129468008513750 : ℤ), (17312407071250 : ℤ), (112841254422250 : ℤ)],
        ![(-58102023436125 : ℤ), (-20272736769625 : ℤ), (112841254422250 : ℤ), (66919732760500 : ℤ)]],
      ![![(26711236103289 : ℤ), (-70692733739875 : ℤ), (63451720541250 : ℤ), (-3030889265375 : ℤ)],
        ![(-70692733739875 : ℤ), (164926663710750 : ℤ), (-129468008513750 : ℤ), (39781753961625 : ℤ)],
        ![(63451720541250 : ℤ), (-129468008513750 : ℤ), (17312407071250 : ℤ), (-3369116475500 : ℤ)],
        ![(-58102023436125 : ℤ), (-20272736769625 : ℤ), (112841254422250 : ℤ), (-79744176489750 : ℤ)]],
      ![![(26711236103289 : ℤ), (-70692733739875 : ℤ), (63451720541250 : ℤ), (-58102023436125 : ℤ)],
        ![(-70692733739875 : ℤ), (164926663710750 : ℤ), (-129468008513750 : ℤ), (-20272736769625 : ℤ)],
        ![(63451720541250 : ℤ), (-129468008513750 : ℤ), (17312407071250 : ℤ), (112841254422250 : ℤ)],
        ![(-3030889265375 : ℤ), (39781753961625 : ℤ), (-3369116475500 : ℤ), (-79744176489750 : ℤ)]],
      ![![(26711236103289 : ℤ), (-70692733739875 : ℤ), (63451720541250 : ℤ), (-3030889265375 : ℤ)],
        ![(-70692733739875 : ℤ), (164926663710750 : ℤ), (-129468008513750 : ℤ), (39781753961625 : ℤ)],
        ![(63451720541250 : ℤ), (-129468008513750 : ℤ), (17312407071250 : ℤ), (-3369116475500 : ℤ)],
        ![(-3030889265375 : ℤ), (39781753961625 : ℤ), (-3369116475500 : ℤ), (-548649595000 : ℤ)]]],
    ![
      ![![(28967238844039 : ℤ), (-74269839581625 : ℤ), (64589164084750 : ℤ), (-56680791053000 : ℤ)],
        ![(-74269839581625 : ℤ), (173511656028000 : ℤ), (-141840880541625 : ℤ), (-27661917408000 : ℤ)],
        ![(64589164084750 : ℤ), (-141840880541625 : ℤ), (26233467013250 : ℤ), (118274011768500 : ℤ)],
        ![(-56680791053000 : ℤ), (-27661917408000 : ℤ), (118274011768500 : ℤ), (73563907614750 : ℤ)]],
      ![![(28967238844039 : ℤ), (-74269839581625 : ℤ), (64589164084750 : ℤ), (-405887963250 : ℤ)],
        ![(-74269839581625 : ℤ), (173511656028000 : ℤ), (-141840880541625 : ℤ), (47342410344500 : ℤ)],
        ![(64589164084750 : ℤ), (-141840880541625 : ℤ), (26233467013250 : ℤ), (-9346667464250 : ℤ)],
        ![(-56680791053000 : ℤ), (-27661917408000 : ℤ), (118274011768500 : ℤ), (-85254905888250 : ℤ)]],
      ![![(28967238844039 : ℤ), (-74269839581625 : ℤ), (64589164084750 : ℤ), (-56680791053000 : ℤ)],
        ![(-74269839581625 : ℤ), (173511656028000 : ℤ), (-141840880541625 : ℤ), (-27661917408000 : ℤ)],
        ![(64589164084750 : ℤ), (-141840880541625 : ℤ), (26233467013250 : ℤ), (118274011768500 : ℤ)],
        ![(-405887963250 : ℤ), (47342410344500 : ℤ), (-9346667464250 : ℤ), (-85254905888250 : ℤ)]],
      ![![(28967238844039 : ℤ), (-74269839581625 : ℤ), (64589164084750 : ℤ), (-405887963250 : ℤ)],
        ![(-74269839581625 : ℤ), (173511656028000 : ℤ), (-141840880541625 : ℤ), (47342410344500 : ℤ)],
        ![(64589164084750 : ℤ), (-141840880541625 : ℤ), (26233467013250 : ℤ), (-9346667464250 : ℤ)],
        ![(-405887963250 : ℤ), (47342410344500 : ℤ), (-9346667464250 : ℤ), (858773924250 : ℤ)]]]]

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
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (-360 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (-348 : ℤ)
                                  Certificate.inside
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (-342 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside))
                                Certificate.inside))
                            Certificate.inside)
                          Certificate.inside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (-360 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (-348 : ℤ)
                                Certificate.inside
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (-342 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside))
                              Certificate.inside))
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              Certificate.inside))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.cross (-234839814297073 : ℤ) (329853488332800 : ℕ) none)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                (Certificate.cross (-234839814297073 : ℤ) (329853488332800 : ℕ) none))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (-341898001812556141 : ℤ) (450359962737049600 : ℕ) none)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (-341898001812556141 : ℤ) (450359962737049600 : ℕ) none)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-9565471222132852009 : ℤ) (10808639105689190400 : ℕ) none)
                        (Certificate.cross (-9598939898050672009 : ℤ) (10808639105689190400 : ℕ) none))))
                  (Certificate.cross (-208055368579448503 : ℤ) (225179981368524800 : ℕ) none))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.cross (-208055368579448503 : ℤ) (225179981368524800 : ℕ) none)
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
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)))))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.cross (-466332175914595891 : ℤ) (450359962737049600 : ℕ) none)
                    (Certificate.cross (-2058854771340400649 : ℤ) (1801439850948198400 : ℕ) none))
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-744 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-392032363233594363929 : ℤ) (461168601842738790400 : ℕ) none)))
                          (Certificate.cross (-155595007315890505067 : ℤ) (230584300921369395200 : ℕ) none))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-696 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              (Certificate.splitX (-708 : ℤ)
                                (Certificate.splitY (204 : ℤ)
                                  Certificate.inside
                                  (Certificate.cross (-147873925890371112714449 : ℤ) (118059162071741130342400 : ℕ) none))
                                (Certificate.splitY (204 : ℤ)
                                  (Certificate.cross (-50581517496152832398429 : ℤ) (44272185776902923878400 : ℕ) none)
                                  (Certificate.cross (-167596611329863235979287 : ℤ) (132816557330708771635200 : ℕ) none)))
                              (Certificate.cross (-15837874955757495327557 : ℤ) (12912720851596686131200 : ℕ) none))
                            (Certificate.cross (-296753483981377231163 : ℤ) (201761263306198220800 : ℕ) none))
                          Certificate.outside))
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-130311890139211157 : ℤ) (126663739519795200 : ℕ) none)
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
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
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
                          Certificate.outside
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-132 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (-126 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))))
                            Certificate.outside))))
                    Certificate.outside))))))),
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
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)))))
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.cross (-466332175914595891 : ℤ) (450359962737049600 : ℕ) none)
                      (Certificate.cross (-2058854771340400649 : ℤ) (1801439850948198400 : ℕ) none)))
                  (Certificate.cross (-130311890139211157 : ℤ) (126663739519795200 : ℕ) none))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-720 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-392032363233594363929 : ℤ) (461168601842738790400 : ℕ) none))
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.splitY (-696 : ℤ)
                              (Certificate.splitX (204 : ℤ)
                                (Certificate.cross (-50581517496152832398429 : ℤ) (44272185776902923878400 : ℕ) none)
                                (Certificate.splitY (-708 : ℤ)
                                  (Certificate.cross (-147873925890371112714449 : ℤ) (118059162071741130342400 : ℕ) none)
                                  (Certificate.cross (-167596611329863235979287 : ℤ) (132816557330708771635200 : ℕ) none)))
                              (Certificate.cross (-4174349588886290657483 : ℤ) (3228180212899171532800 : ℕ) none))
                            (Certificate.cross (-2039174481319398622429 : ℤ) (1614090106449585766400 : ℕ) none)))
                        (Certificate.cross (-103589729523224089899 : ℤ) (100880631653099110400 : ℕ) none))
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
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    Certificate.outside))))
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
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
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
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (-126 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))))
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
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside))
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
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                Certificate.outside))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside)))
          Certificate.outside)
        (Certificate.splitY (768 : ℤ)
          Certificate.outside
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (960 : ℤ)
                Certificate.outside
                (Certificate.splitY (960 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1056 : ℤ)
                    Certificate.outside
                    Certificate.outside)))
              (Certificate.splitX (960 : ℤ)
                Certificate.outside
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (1056 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1248 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)))
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1248 : ℤ)
                    Certificate.outside
                    Certificate.outside))
                Certificate.outside)
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (1248 : ℤ)
                      (Certificate.splitX (1200 : ℤ)
                        (Certificate.splitY (1200 : ℤ)
                          (Certificate.splitX (1176 : ℤ)
                            (Certificate.splitY (1176 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (1176 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1188 : ℤ)
                                Certificate.outside
                                Certificate.outside)))
                          Certificate.outside)
                        (Certificate.splitY (1200 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (1248 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                Certificate.outside)))))],
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (-312 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (-324 : ℤ)
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (-330 : ℤ)
                                      Certificate.inside
                                      (Certificate.splitX (-1533 : ℤ)
                                        (Certificate.splitY (-327 : ℤ)
                                          Certificate.inside
                                          Certificate.inside)
                                        Certificate.inside))
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside))
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                Certificate.inside))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (-312 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (-324 : ℤ)
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (-330 : ℤ)
                                    Certificate.inside
                                    (Certificate.splitY (-1530 : ℤ)
                                      (Certificate.splitX (-327 : ℤ)
                                        Certificate.inside
                                        Certificate.inside)
                                      Certificate.inside))
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside))
                      Certificate.inside)
                    Certificate.inside)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                Certificate.inside)))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.cross (-1190096033172563 : ℤ) (1759218604441600 : ℕ) none)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                (Certificate.cross (-1190096033172563 : ℤ) (1759218604441600 : ℕ) none))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (-211200346273591673 : ℤ) (450359962737049600 : ℕ) none)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (-211200346273591673 : ℤ) (450359962737049600 : ℕ) none)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-3081359758893825199 : ℤ) (3602879701896396800 : ℕ) none)
                        (Certificate.cross (-3101279359321797939 : ℤ) (3602879701896396800 : ℕ) none))))
                  (Certificate.cross (-51200471421106251 : ℤ) (56294995342131200 : ℕ) none))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.cross (-51200471421106251 : ℤ) (56294995342131200 : ℕ) none)
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
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.cross (-285776828555064173 : ℤ) (450359962737049600 : ℕ) none)
                    (Certificate.cross (-513519463462526383 : ℤ) (450359962737049600 : ℕ) none))
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.cross (-64214128115201166163 : ℤ) (403522526612396441600 : ℕ) none))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-696 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              (Certificate.splitX (-708 : ℤ)
                                Certificate.inside
                                (Certificate.splitY (204 : ℤ)
                                  Certificate.inside
                                  (Certificate.cross (-4501425335759981680201 : ℤ) (3689348814741910323200 : ℕ) none)))
                              (Certificate.cross (-17259725633607846504739 : ℤ) (14757395258967641292800 : ℕ) none))
                            (Certificate.splitY (216 : ℤ)
                              (Certificate.splitX (-684 : ℤ)
                                (Certificate.splitY (204 : ℤ)
                                  (Certificate.cross (-1049191917112933379681671 : ℤ) (944473296573929042739200 : ℕ) none)
                                  (Certificate.cross (-73304932331902332376831 : ℤ) (59029581035870565171200 : ℕ) none))
                                (Certificate.cross (-30604045887689359432739 : ℤ) (23980767295822417100800 : ℕ) none))
                              Certificate.outside))
                          Certificate.outside))
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-115750938395498657 : ℤ) (112589990684262400 : ℕ) none)
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
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)
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
                          Certificate.outside
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-132 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (-126 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))))
                            Certificate.outside))))
                    Certificate.outside))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.cross (-285776828555064173 : ℤ) (450359962737049600 : ℕ) none)
                      (Certificate.cross (-513519463462526383 : ℤ) (450359962737049600 : ℕ) none)))
                  (Certificate.cross (-115750938395498657 : ℤ) (112589990684262400 : ℕ) none))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-720 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.splitY (-696 : ℤ)
                              (Certificate.splitX (204 : ℤ)
                                Certificate.inside
                                (Certificate.cross (-4501425335759981680201 : ℤ) (3689348814741910323200 : ℕ) none))
                              (Certificate.splitX (204 : ℤ)
                                (Certificate.cross (-6239356713493291617233 : ℤ) (5303438921191496089600 : ℕ) none)
                                (Certificate.cross (-14950164081155596834057 : ℤ) (11990383647911208550400 : ℕ) none)))
                            (Certificate.cross (-427840343343410790259 : ℤ) (345876451382054092800 : ℕ) none)))
                        (Certificate.cross (-245406871576940253197 : ℤ) (244995819728954982400 : ℕ) none))
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
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    Certificate.outside))))
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
                  (Certificate.splitX (864 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
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
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (-126 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))))
                              Certificate.outside))))
                      Certificate.outside)))))))),
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
                      Certificate.outside))
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
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        Certificate.outside)))))
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
                        Certificate.outside
                        Certificate.outside)))
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (624 : ℤ)
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (648 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      Certificate.outside)
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (720 : ℤ)
                        (Certificate.splitY (720 : ℤ)
                          (Certificate.splitX (696 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside)
                        (Certificate.splitY (720 : ℤ)
                          Certificate.outside
                          Certificate.outside))))))))
          (Certificate.splitX (384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (576 : ℤ)
                Certificate.outside
                Certificate.outside)
              Certificate.outside)))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
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
              Certificate.inside
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (-360 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (-348 : ℤ)
                                  Certificate.inside
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (-342 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside))
                                Certificate.inside))
                            Certificate.inside)
                          Certificate.inside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                Certificate.inside))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (-360 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (-348 : ℤ)
                                Certificate.inside
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (-342 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside))
                              Certificate.inside))
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                Certificate.inside)))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.cross (-274342534614297 : ℤ) (384829069721600 : ℕ) none)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                (Certificate.cross (-274342534614297 : ℤ) (384829069721600 : ℕ) none))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-790460070737615439 : ℤ) (900719925474099200 : ℕ) none)
                        (Certificate.cross (-1605981193910828673 : ℤ) (1801439850948198400 : ℕ) none))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (-11771556130451021 : ℤ) (14073748835532800 : ℕ) none)
                    (Certificate.cross (-195914418142879131 : ℤ) (225179981368524800 : ℕ) none)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (-1105214432695303891 : ℤ) (1351079888211148800 : ℕ) none)
                      (Certificate.cross (-195914418142879131 : ℤ) (225179981368524800 : ℕ) none))
                    (Certificate.cross (-74139871596494251 : ℤ) (84442493013196800 : ℕ) none))
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
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-672 : ℤ)
                    Certificate.inside
                    (Certificate.cross (-550695305554510137 : ℤ) (450359962737049600 : ℕ) none))
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.cross (-2876005770110143631 : ℤ) (3602879701896396800 : ℕ) none)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-696 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-801921902216585087661 : ℤ) (922337203685477580800 : ℕ) none))
                            (Certificate.splitY (216 : ℤ)
                              (Certificate.splitX (-684 : ℤ)
                                (Certificate.splitY (204 : ℤ)
                                  Certificate.inside
                                  (Certificate.cross (-35915893172540461664787 : ℤ) (29514790517935282585600 : ℕ) none))
                                (Certificate.splitY (204 : ℤ)
                                  (Certificate.cross (-930992113093608480429 : ℤ) (807045053224792883200 : ℕ) none)
                                  (Certificate.cross (-1186947267335060102161 : ℤ) (922337203685477580800 : ℕ) none)))
                              (Certificate.cross (-289962067203354326509 : ℤ) (230584300921369395200 : ℕ) none)))
                          (Certificate.cross (-95972963097253105161 : ℤ) (93674872249306316800 : ℕ) none)))
                      (Certificate.cross (-8956268602699743567 : ℤ) (25220157913274777600 : ℕ) none))
                    (Certificate.cross (-556160791667011879 : ℤ) (337769972052787200 : ℕ) none)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-27997847575422633 : ℤ) (24629060462182400 : ℕ) none)
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
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)
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
                          Certificate.outside
                          (Certificate.splitX (-120 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-108 : ℤ)
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (-114 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))
                                Certificate.outside))))))
                    Certificate.outside))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-672 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-550695305554510137 : ℤ) (450359962737049600 : ℕ) none)))
                  (Certificate.cross (-27997847575422633 : ℤ) (24629060462182400 : ℕ) none))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-720 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.splitY (-696 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (204 : ℤ)
                                (Certificate.cross (-930992113093608480429 : ℤ) (807045053224792883200 : ℕ) none)
                                (Certificate.cross (-1053705157532068511679 : ℤ) (807045053224792883200 : ℕ) none)))
                            (Certificate.cross (-75787020966249508701 : ℤ) (57646075230342348800 : ℕ) none)))
                        (Certificate.cross (-95972963097253105161 : ℤ) (93674872249306316800 : ℕ) none))
                      (Certificate.cross (-2908107841802820423 : ℤ) (1801439850948198400 : ℕ) none))
                    (Certificate.cross (-4752243081198703899 : ℤ) (6530219459687219200 : ℕ) none))
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
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    Certificate.outside))))
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
                  (Certificate.splitX (864 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
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
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            (Certificate.splitY (-120 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-120 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-108 : ℤ)
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (-114 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))
                                  Certificate.outside))))))
                      Certificate.outside)))))))),
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
        (Certificate.splitY (768 : ℤ)
          Certificate.outside
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
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (-360 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (-372 : ℤ)
                                  Certificate.inside
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (-366 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside))
                                Certificate.inside)
                              Certificate.inside)
                            (Certificate.splitY (-360 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                Certificate.inside))
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              Certificate.inside
              Certificate.inside)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (-360 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (-372 : ℤ)
                                Certificate.inside
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (-366 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside))
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside)
              Certificate.inside))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.cross (-625158214881313 : ℤ) (1319413953331200 : ℕ) none))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-625158214881313 : ℤ) (1319413953331200 : ℕ) none)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-3485801906113000721 : ℤ) (4053239664633446400 : ℕ) none)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-3485801906113000721 : ℤ) (4053239664633446400 : ℕ) none)
                          (Certificate.cross (-6499827287338660759 : ℤ) (7205759403792793600 : ℕ) none)))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (-374117994399694253 : ℤ) (478507460408115200 : ℕ) none)
                    (Certificate.cross (-177426360443913003 : ℤ) (197032483697459200 : ℕ) none)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (-8160801537742963721 : ℤ) (10808639105689190400 : ℕ) none)
                      (Certificate.cross (-177426360443913003 : ℤ) (197032483697459200 : ℕ) none))
                    (Certificate.cross (-102894948267934157 : ℤ) (119626865102028800 : ℕ) none))
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
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-15621482243046407 : ℤ) (14073748835532800 : ℕ) none)
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-696 : ℤ)
                            (Certificate.cross (-216873996411057692429 : ℤ) (691752902764108185600 : ℕ) none)
                            (Certificate.splitY (216 : ℤ)
                              (Certificate.cross (-89413740261639024163 : ℤ) (86469112845513523200 : ℕ) none)
                              (Certificate.splitX (-684 : ℤ)
                                (Certificate.splitY (228 : ℤ)
                                  (Certificate.cross (-389065854332592448886023 : ℤ) (354177486215223391027200 : ℕ) none)
                                  (Certificate.cross (-181996634526773099529537 : ℤ) (162331347848644054220800 : ℕ) none))
                                (Certificate.splitY (228 : ℤ)
                                  (Certificate.cross (-1141679821220842202027 : ℤ) (922337203685477580800 : ℕ) none)
                                  Certificate.outside))))
                          (Certificate.cross (-71091281203832850911 : ℤ) (64851834634135142400 : ℕ) none)))
                      (Certificate.cross (-8010613568202462817 : ℤ) (21617278211378380800 : ℕ) none))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-624 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-648 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              (Certificate.cross (-7165161431556342795483 : ℤ) (5995191823955604275200 : ℕ) none)
                              Certificate.outside)
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-343741900355221003 : ℤ) (337769972052787200 : ℕ) none)
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
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
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
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-84 : ℤ)
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (-90 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))
                                Certificate.outside))
                            Certificate.outside))
                        Certificate.outside))))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.cross (-15621482243046407 : ℤ) (14073748835532800 : ℕ) none)
                  (Certificate.cross (-343741900355221003 : ℤ) (337769972052787200 : ℕ) none))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-720 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.cross (-89413740261639024163 : ℤ) (86469112845513523200 : ℕ) none)
                            (Certificate.splitY (-696 : ℤ)
                              (Certificate.cross (-216873996411057692429 : ℤ) (691752902764108185600 : ℕ) none)
                              (Certificate.splitX (228 : ℤ)
                                (Certificate.cross (-1141679821220842202027 : ℤ) (922337203685477580800 : ℕ) none)
                                (Certificate.cross (-2925470548973512497929 : ℤ) (2421135159674378649600 : ℕ) none)))))
                        (Certificate.cross (-71091281203832850911 : ℤ) (64851834634135142400 : ℕ) none))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-624 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.cross (-910457757886616037201 : ℤ) (749398977994450534400 : ℕ) none)
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.cross (-4670902299150219149 : ℤ) (6079859496950169600 : ℕ) none))
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
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    Certificate.outside))))
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
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
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
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-84 : ℤ)
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (-90 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))
                                  Certificate.outside))
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
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
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
        (Certificate.splitY (768 : ℤ)
          Certificate.outside
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
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (-360 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (-348 : ℤ)
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (-354 : ℤ)
                                      Certificate.inside
                                      (Certificate.splitX (-1533 : ℤ)
                                        (Certificate.splitY (-351 : ℤ)
                                          Certificate.inside
                                          Certificate.inside)
                                        Certificate.inside))
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside))
                            Certificate.inside)
                          Certificate.inside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-1392 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (-360 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (-348 : ℤ)
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (-354 : ℤ)
                                    Certificate.inside
                                    (Certificate.splitY (-1530 : ℤ)
                                      (Certificate.splitX (-351 : ℤ)
                                        Certificate.inside
                                        Certificate.inside)
                                      Certificate.inside))
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside))
                          Certificate.inside)
                        Certificate.inside)
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              Certificate.inside))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.cross (-72760526676961 : ℤ) (137438953472000 : ℕ) none))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-72760526676961 : ℤ) (137438953472000 : ℕ) none)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-3881311992980124317 : ℤ) (4503599627370496000 : ℕ) none)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-3881311992980124317 : ℤ) (4503599627370496000 : ℕ) none)
                          (Certificate.cross (-2082492261501124673 : ℤ) (2251799813685248000 : ℕ) none)))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (-44130595842160891 : ℤ) (52776558133248000 : ℕ) none)
                    (Certificate.cross (-263118303309980131 : ℤ) (281474976710656000 : ℕ) none)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (-14378238061168342067 : ℤ) (18014398509481984000 : ℕ) none)
                      (Certificate.cross (-263118303309980131 : ℤ) (281474976710656000 : ℕ) none))
                    (Certificate.cross (-1529445833108242637 : ℤ) (1688849860263936000 : ℕ) none))
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
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-672 : ℤ)
                    Certificate.inside
                    (Certificate.cross (-337562564193790381 : ℤ) (281474976710656000 : ℕ) none))
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-696 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-26810232076882650197 : ℤ) (36028797018963968000 : ℕ) none)))
                          (Certificate.cross (-22985426241342740161 : ℤ) (36028797018963968000 : ℕ) none)))
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-624 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-648 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              (Certificate.splitX (-660 : ℤ)
                                (Certificate.cross (-43322180889512782004581 : ℤ) (36893488147419103232000 : ℕ) none)
                                (Certificate.splitY (204 : ℤ)
                                  (Certificate.cross (-40284027993821171248081 : ℤ) (36893488147419103232000 : ℕ) none)
                                  (Certificate.cross (-47745390529753776796853 : ℤ) (36893488147419103232000 : ℕ) none)))
                              (Certificate.cross (-23195480760059946080057 : ℤ) (18446744073709551616000 : ℕ) none))
                            (Certificate.cross (-113785840597383065269 : ℤ) (72057594037927936000 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-4995509154883877 : ℤ) (4398046511104000 : ℕ) none)
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
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)
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
                      Certificate.outside
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-120 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-108 : ℤ)
                                Certificate.outside
                                Certificate.outside))))))
                    Certificate.outside))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-672 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-337562564193790381 : ℤ) (281474976710656000 : ℕ) none)))
                  (Certificate.cross (-4995509154883877 : ℤ) (4398046511104000 : ℕ) none))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-720 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (216 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-26810232076882650197 : ℤ) (36028797018963968000 : ℕ) none)))
                        (Certificate.cross (-22985426241342740161 : ℤ) (36028797018963968000 : ℕ) none))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-624 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.splitY (-648 : ℤ)
                              (Certificate.splitX (204 : ℤ)
                                (Certificate.cross (-40284027993821171248081 : ℤ) (36893488147419103232000 : ℕ) none)
                                (Certificate.cross (-3038680914429262883341 : ℤ) (2305843009213693952000 : ℕ) none))
                              (Certificate.cross (-1549398263997097397929 : ℤ) (1152921504606846976000 : ℕ) none))
                            (Certificate.cross (-378374448249611314951 : ℤ) (288230376151711744000 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.cross (-4021174039441417399 : ℤ) (5629499534213120000 : ℕ) none))
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
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    Certificate.outside))))
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
                  (Certificate.splitX (864 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
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
                      Certificate.outside
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
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
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
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside))
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
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        Certificate.outside)))))
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                Certificate.outside))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside)
              (Certificate.splitX (576 : ℤ)
                Certificate.outside
                Certificate.outside)))
          Certificate.outside)
        (Certificate.splitY (768 : ℤ)
          Certificate.outside
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

end BerryEsseen.N2NeededIntegerPointwise01

#print axioms BerryEsseen.N2NeededIntegerPointwise01.powers_entries
#print axioms BerryEsseen.N2NeededIntegerPointwise01.powers_eq
#print axioms BerryEsseen.N2NeededIntegerPointwise01.checks
#print axioms BerryEsseen.N2NeededIntegerPointwise01.pointwise
