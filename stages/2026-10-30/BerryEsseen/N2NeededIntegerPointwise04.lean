module

public import BerryEsseen.N2NeededIntegerData
public import BerryEsseen.N2IntegerPointwiseReplay

@[expose] public section

/-! 2026-10-29: integer power numerators and the unchanged original
rows025..029 closed trees. The entries equality is the semantic cache bridge.
No Bernstein coefficient or host closed flag is a premise. -/

namespace BerryEsseen.N2NeededIntegerPointwise04

open N2NeededData N2NeededIntegerData N2IntegerBernstein
  N2IntegerRectangleCertificate N2MajorantPolynomials

def rowIndex (j : Fin 5) : Fin 65 :=
  ⟨4 * 5 + j.val,
    lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (4 * 5)) (by decide)⟩

def signX : Fin 4 → ℚ := N2IntegerPointwiseReplay.signX
def signY : Fin 4 → ℚ := N2IntegerPointwiseReplay.signY

def powers : Fin 5 → Fin 4 → IntPower :=
  ![
    ![
      ![![(248281698810539 : ℤ), (-279163635699500 : ℤ), (58330827348250 : ℤ), (7953427732500 : ℤ)],
        ![(-279163635699500 : ℤ), (65083596290875 : ℤ), (206568810029000 : ℤ), (67275917409125 : ℤ)],
        ![(58330827348250 : ℤ), (206568810029000 : ℤ), (-284178233462375 : ℤ), (-90577268355250 : ℤ)],
        ![(7953427732500 : ℤ), (67275917409125 : ℤ), (-90577268355250 : ℤ), (-6864988955375 : ℤ)]],
      ![![(248281698810539 : ℤ), (-279163635699500 : ℤ), (58330827348250 : ℤ), (16161726067750 : ℤ)],
        ![(-279163635699500 : ℤ), (65083596290875 : ℤ), (206568810029000 : ℤ), (-80611955044625 : ℤ)],
        ![(58330827348250 : ℤ), (206568810029000 : ℤ), (-284178233462375 : ℤ), (71814559564000 : ℤ)],
        ![(7953427732500 : ℤ), (67275917409125 : ℤ), (-90577268355250 : ℤ), (9745988969625 : ℤ)]],
      ![![(248281698810539 : ℤ), (-279163635699500 : ℤ), (58330827348250 : ℤ), (7953427732500 : ℤ)],
        ![(-279163635699500 : ℤ), (65083596290875 : ℤ), (206568810029000 : ℤ), (67275917409125 : ℤ)],
        ![(58330827348250 : ℤ), (206568810029000 : ℤ), (-284178233462375 : ℤ), (-90577268355250 : ℤ)],
        ![(16161726067750 : ℤ), (-80611955044625 : ℤ), (71814559564000 : ℤ), (9745988969625 : ℤ)]],
      ![![(248281698810539 : ℤ), (-279163635699500 : ℤ), (58330827348250 : ℤ), (16161726067750 : ℤ)],
        ![(-279163635699500 : ℤ), (65083596290875 : ℤ), (206568810029000 : ℤ), (-80611955044625 : ℤ)],
        ![(58330827348250 : ℤ), (206568810029000 : ℤ), (-284178233462375 : ℤ), (71814559564000 : ℤ)],
        ![(16161726067750 : ℤ), (-80611955044625 : ℤ), (71814559564000 : ℤ), (-13701944910375 : ℤ)]]],
    ![
      ![![(268154583435914 : ℤ), (-280462774523375 : ℤ), (32952079338500 : ℤ), (8020663376250 : ℤ)],
        ![(-280462774523375 : ℤ), (61062605641000 : ℤ), (198910145441750 : ℤ), (54575750417000 : ℤ)],
        ![(32952079338500 : ℤ), (198910145441750 : ℤ), (-223518266074875 : ℤ), (-77452084983750 : ℤ)],
        ![(8020663376250 : ℤ), (54575750417000 : ℤ), (-77452084983750 : ℤ), (0 : ℤ)]],
      ![![(268154583435914 : ℤ), (-280462774523375 : ℤ), (32952079338500 : ℤ), (28214118707000 : ℤ)],
        ![(-280462774523375 : ℤ), (61062605641000 : ℤ), (198910145441750 : ℤ), (-72762158902500 : ℤ)],
        ![(32952079338500 : ℤ), (198910145441750 : ℤ), (-223518266074875 : ℤ), (41217302900500 : ℤ)],
        ![(8020663376250 : ℤ), (54575750417000 : ℤ), (-77452084983750 : ℤ), (0 : ℤ)]],
      ![![(268154583435914 : ℤ), (-280462774523375 : ℤ), (32952079338500 : ℤ), (8020663376250 : ℤ)],
        ![(-280462774523375 : ℤ), (61062605641000 : ℤ), (198910145441750 : ℤ), (54575750417000 : ℤ)],
        ![(32952079338500 : ℤ), (198910145441750 : ℤ), (-223518266074875 : ℤ), (-77452084983750 : ℤ)],
        ![(28214118707000 : ℤ), (-72762158902500 : ℤ), (41217302900500 : ℤ), (0 : ℤ)]],
      ![![(268154583435914 : ℤ), (-280462774523375 : ℤ), (32952079338500 : ℤ), (28214118707000 : ℤ)],
        ![(-280462774523375 : ℤ), (61062605641000 : ℤ), (198910145441750 : ℤ), (-72762158902500 : ℤ)],
        ![(32952079338500 : ℤ), (198910145441750 : ℤ), (-223518266074875 : ℤ), (41217302900500 : ℤ)],
        ![(28214118707000 : ℤ), (-72762158902500 : ℤ), (41217302900500 : ℤ), (0 : ℤ)]]],
    ![
      ![![(333021769209789 : ℤ), (-247287410423625 : ℤ), (-44787951450000 : ℤ), (-17143743961375 : ℤ)],
        ![(-247287410423625 : ℤ), (60777456103000 : ℤ), (151358928417000 : ℤ), (33893275868875 : ℤ)],
        ![(-44787951450000 : ℤ), (151358928417000 : ℤ), (-127414681071250 : ℤ), (-51612370713250 : ℤ)],
        ![(-17143743961375 : ℤ), (33893275868875 : ℤ), (-51612370713250 : ℤ), (0 : ℤ)]],
      ![![(333021769209789 : ℤ), (-247287410423625 : ℤ), (-44787951450000 : ℤ), (47909164266625 : ℤ)],
        ![(-247287410423625 : ℤ), (60777456103000 : ℤ), (151358928417000 : ℤ), (-53465265149875 : ℤ)],
        ![(-44787951450000 : ℤ), (151358928417000 : ℤ), (-127414681071250 : ℤ), (20846950408000 : ℤ)],
        ![(-17143743961375 : ℤ), (33893275868875 : ℤ), (-51612370713250 : ℤ), (0 : ℤ)]],
      ![![(333021769209789 : ℤ), (-247287410423625 : ℤ), (-44787951450000 : ℤ), (-17143743961375 : ℤ)],
        ![(-247287410423625 : ℤ), (60777456103000 : ℤ), (151358928417000 : ℤ), (33893275868875 : ℤ)],
        ![(-44787951450000 : ℤ), (151358928417000 : ℤ), (-127414681071250 : ℤ), (-51612370713250 : ℤ)],
        ![(47909164266625 : ℤ), (-53465265149875 : ℤ), (20846950408000 : ℤ), (0 : ℤ)]],
      ![![(333021769209789 : ℤ), (-247287410423625 : ℤ), (-44787951450000 : ℤ), (47909164266625 : ℤ)],
        ![(-247287410423625 : ℤ), (60777456103000 : ℤ), (151358928417000 : ℤ), (-53465265149875 : ℤ)],
        ![(-44787951450000 : ℤ), (151358928417000 : ℤ), (-127414681071250 : ℤ), (20846950408000 : ℤ)],
        ![(47909164266625 : ℤ), (-53465265149875 : ℤ), (20846950408000 : ℤ), (0 : ℤ)]]],
    ![
      ![![(329077250986914 : ℤ), (-256384683205750 : ℤ), (-33838032230250 : ℤ), (-8855709157375 : ℤ)],
        ![(-256384683205750 : ℤ), (58601495493250 : ℤ), (159792531136125 : ℤ), (33745493180375 : ℤ)],
        ![(-33838032230250 : ℤ), (159792531136125 : ℤ), (-139719160008875 : ℤ), (-59224950663625 : ℤ)],
        ![(-8855709157375 : ℤ), (33745493180375 : ℤ), (-59224950663625 : ℤ), (0 : ℤ)]],
      ![![(329077250986914 : ℤ), (-256384683205750 : ℤ), (-33838032230250 : ℤ), (45175454508875 : ℤ)],
        ![(-256384683205750 : ℤ), (58601495493250 : ℤ), (159792531136125 : ℤ), (-55484541406375 : ℤ)],
        ![(-33838032230250 : ℤ), (159792531136125 : ℤ), (-139719160008875 : ℤ), (22905205312125 : ℤ)],
        ![(-8855709157375 : ℤ), (33745493180375 : ℤ), (-59224950663625 : ℤ), (0 : ℤ)]],
      ![![(329077250986914 : ℤ), (-256384683205750 : ℤ), (-33838032230250 : ℤ), (-8855709157375 : ℤ)],
        ![(-256384683205750 : ℤ), (58601495493250 : ℤ), (159792531136125 : ℤ), (33745493180375 : ℤ)],
        ![(-33838032230250 : ℤ), (159792531136125 : ℤ), (-139719160008875 : ℤ), (-59224950663625 : ℤ)],
        ![(45175454508875 : ℤ), (-55484541406375 : ℤ), (22905205312125 : ℤ), (0 : ℤ)]],
      ![![(329077250986914 : ℤ), (-256384683205750 : ℤ), (-33838032230250 : ℤ), (45175454508875 : ℤ)],
        ![(-256384683205750 : ℤ), (58601495493250 : ℤ), (159792531136125 : ℤ), (-55484541406375 : ℤ)],
        ![(-33838032230250 : ℤ), (159792531136125 : ℤ), (-139719160008875 : ℤ), (22905205312125 : ℤ)],
        ![(45175454508875 : ℤ), (-55484541406375 : ℤ), (22905205312125 : ℤ), (0 : ℤ)]]],
    ![
      ![![(332728604705664 : ℤ), (-260474619435250 : ℤ), (-34121855950625 : ℤ), (-10477191653500 : ℤ)],
        ![(-260474619435250 : ℤ), (54808728035750 : ℤ), (162925862716000 : ℤ), (35129336865500 : ℤ)],
        ![(-34121855950625 : ℤ), (162925862716000 : ℤ), (-136994487064000 : ℤ), (-57064364585250 : ℤ)],
        ![(-10477191653500 : ℤ), (35129336865500 : ℤ), (-57064364585250 : ℤ), (0 : ℤ)]],
      ![![(332728604705664 : ℤ), (-260474619435250 : ℤ), (-34121855950625 : ℤ), (45469608530750 : ℤ)],
        ![(-260474619435250 : ℤ), (54808728035750 : ℤ), (162925862716000 : ℤ), (-55951916384250 : ℤ)],
        ![(-34121855950625 : ℤ), (162925862716000 : ℤ), (-136994487064000 : ℤ), (22071947708000 : ℤ)],
        ![(-10477191653500 : ℤ), (35129336865500 : ℤ), (-57064364585250 : ℤ), (0 : ℤ)]],
      ![![(332728604705664 : ℤ), (-260474619435250 : ℤ), (-34121855950625 : ℤ), (-10477191653500 : ℤ)],
        ![(-260474619435250 : ℤ), (54808728035750 : ℤ), (162925862716000 : ℤ), (35129336865500 : ℤ)],
        ![(-34121855950625 : ℤ), (162925862716000 : ℤ), (-136994487064000 : ℤ), (-57064364585250 : ℤ)],
        ![(45469608530750 : ℤ), (-55951916384250 : ℤ), (22071947708000 : ℤ), (0 : ℤ)]],
      ![![(332728604705664 : ℤ), (-260474619435250 : ℤ), (-34121855950625 : ℤ), (45469608530750 : ℤ)],
        ![(-260474619435250 : ℤ), (54808728035750 : ℤ), (162925862716000 : ℤ), (-55951916384250 : ℤ)],
        ![(-34121855950625 : ℤ), (162925862716000 : ℤ), (-136994487064000 : ℤ), (22071947708000 : ℤ)],
        ![(45469608530750 : ℤ), (-55951916384250 : ℤ), (22071947708000 : ℤ), (0 : ℤ)]]]]

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
            Certificate.inside
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            Certificate.inside)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                      (Certificate.cross (-111370044878389 : ℤ) (439804651110400 : ℕ) none))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.cross (-111370044878389 : ℤ) (439804651110400 : ℕ) none))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-168 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-156 : ℤ)
                                (Certificate.cross (-409166260657581051721 : ℤ) (1844674407370955161600 : ℕ) none)
                                (Certificate.cross (-63003672518927655317 : ℤ) (230584300921369395200 : ℕ) none))))
                          (Certificate.cross (-31107865011094862399 : ℤ) (100880631653099110400 : ℕ) none))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-31107865011094862399 : ℤ) (100880631653099110400 : ℕ) none)
                          Certificate.outside))
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
                      Certificate.inside
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (120 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (108 : ℤ)
                                  Certificate.inside
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (114 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside))
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside))
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                Certificate.inside
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
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-624 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-324386285617813471 : ℤ) (450359962737049600 : ℕ) none)))
                      (Certificate.cross (-236554617650053891 : ℤ) (450359962737049600 : ℕ) none))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-5671465692505573 : ℤ) (14073748835532800 : ℕ) none)
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-528 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-112421006877072996317 : ℤ) (230584300921369395200 : ℕ) none)
                          (Certificate.splitX (-552 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              (Certificate.cross (-10545642339910235654663 : ℤ) (14757395258967641292800 : ℕ) none)
                              (Certificate.cross (-11469782205901216319341 : ℤ) (15679732462653118873600 : ℕ) none))
                            (Certificate.cross (-1496445047031924614027 : ℤ) (1959966557831639859200 : ℕ) none)))
                        (Certificate.cross (-62889657957252269411 : ℤ) (79263353441720729600 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside)))
              (Certificate.cross (-1125395945535661 : ℤ) (1759218604441600 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.cross (-2850491173065313 : ℤ) (3078632557772800 : ℕ) none)
                Certificate.outside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-168 : ℤ)
                            Certificate.outside
                            Certificate.outside))
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside))))
          Certificate.outside)),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (108 : ℤ)
                                Certificate.inside
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (114 : ℤ)
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
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                Certificate.inside))
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.cross (-5671465692505573 : ℤ) (14073748835532800 : ℕ) none)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-324386285617813471 : ℤ) (450359962737049600 : ℕ) none)))
                    (Certificate.cross (-236554617650053891 : ℤ) (450359962737049600 : ℕ) none))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.cross (-60086311918086798899 : ℤ) (100880631653099110400 : ℕ) none)
                        (Certificate.splitY (-528 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            (Certificate.cross (-1421194708201447571777 : ℤ) (1959966557831639859200 : ℕ) none)
                            (Certificate.cross (-469745964312545941913 : ℤ) (634106827533765836800 : ℕ) none))
                          Certificate.outside))
                      Certificate.outside)
                    Certificate.outside)))
              (Certificate.splitX (192 : ℤ)
                (Certificate.cross (-520550825023547 : ℤ) (1044536046387200 : ℕ) none)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-1125395945535661 : ℤ) (1759218604441600 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    Certificate.outside)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (456 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside))
                      Certificate.outside)
                    Certificate.outside))
                Certificate.outside))))
        (Certificate.cross (-59206990737487 : ℤ) (769658139443200 : ℕ) none)),
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
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                Certificate.outside)))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (228 : ℤ)
                                Certificate.outside
                                Certificate.outside))))
                        Certificate.outside))
                    Certificate.outside))))
            Certificate.outside))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1248 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (228 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))))
                          Certificate.outside))
                      Certificate.outside))))
              Certificate.outside))
          Certificate.outside))],
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-1152 : ℤ)
            Certificate.inside
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            Certificate.inside)
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
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                      (Certificate.cross (-1795274313392127 : ℤ) (7036874417766400 : ℕ) none))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.cross (-1795274313392127 : ℤ) (7036874417766400 : ℕ) none))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-600938832105885009 : ℤ) (3602879701896396800 : ℕ) none)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-13336209334551251661 : ℤ) (68454714336031539200 : ℕ) none)
                            (Certificate.cross (-4373316364106390067 : ℤ) (15312238733059686400 : ℕ) none)))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (-72217808750165578269 : ℤ) (273818857344126156800 : ℕ) none)
                            (Certificate.cross (-4373316364106390067 : ℤ) (15312238733059686400 : ℕ) none))
                          Certificate.outside))
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
                          Certificate.inside
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (72 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (84 : ℤ)
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (78 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside))
                            Certificate.inside))
                        Certificate.inside)
                      Certificate.inside)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
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
                  (Certificate.cross (-5339937334696629 : ℤ) (14073748835532800 : ℕ) none)
                  (Certificate.cross (-1883068452524063 : ℤ) (2858730232217600 : ℕ) none)))
              (Certificate.cross (-1363606756719969 : ℤ) (2528876743884800 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.cross (-2421863843623063 : ℤ) (2858730232217600 : ℕ) none)
                Certificate.outside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-168 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
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
                        Certificate.inside
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (72 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (84 : ℤ)
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (78 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside))
                          Certificate.inside))
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside)
              Certificate.inside)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.cross (-5339937334696629 : ℤ) (14073748835532800 : ℕ) none)
                (Certificate.cross (-2383196453033251 : ℤ) (3518437208883200 : ℕ) none))
              (Certificate.splitX (192 : ℤ)
                (Certificate.cross (-1010755504232719 : ℤ) (1979120929996800 : ℕ) none)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-1363606756719969 : ℤ) (2528876743884800 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    Certificate.outside)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (456 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
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
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)))
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
                      Certificate.outside))
                  Certificate.outside)
                Certificate.outside)))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                Certificate.outside))
            Certificate.outside))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
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
                  Certificate.outside
                  Certificate.outside))
              Certificate.outside))
          Certificate.outside))],
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-1152 : ℤ)
            Certificate.inside
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            Certificate.inside)
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
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-3150668324314379 : ℤ) (12314530231091200 : ℕ) none))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-3150668324314379 : ℤ) (12314530231091200 : ℕ) none)))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-4970275860596024411 : ℤ) (39631676720860364800 : ℕ) none)
                            (Certificate.cross (-2461103004962879317 : ℤ) (11709359031163289600 : ℕ) none)))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (-2444810322463932229 : ℤ) (14411518807585587200 : ℕ) none)
                            (Certificate.cross (-2461103004962879317 : ℤ) (11709359031163289600 : ℕ) none))
                          (Certificate.cross (-408678028351323637 : ℤ) (1576259869579673600 : ℕ) none)))
                      (Certificate.cross (-66250499491350907 : ℤ) (204069358115225600 : ℕ) none))
                    (Certificate.cross (-216734044678211 : ℤ) (604731395276800 : ℕ) none)))))))),
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
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-432 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-456 : ℤ)
                            (Certificate.cross (-6157918474325894009 : ℤ) (9907919180215091200 : ℕ) none)
                            (Certificate.cross (-4543462590635913067 : ℤ) (7205759403792793600 : ℕ) none)))
                        (Certificate.cross (-1835048312408045923 : ℤ) (2927339757790822400 : ℕ) none))))
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.cross (-295961365711708631 : ℤ) (506654958079180800 : ℕ) none)
                    (Certificate.cross (-293724006257013 : ℤ) (439804651110400 : ℕ) none))))
              (Certificate.cross (-5299059113425751 : ℤ) (9675702324428800 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-1162304431926233399 : ℤ) (3152519739159347200 : ℕ) none)
                      (Certificate.cross (-2107889809750519 : ℤ) (3518437208883200 : ℕ) none))
                    (Certificate.cross (-875344992012687881 : ℤ) (1632554864921804800 : ℕ) none))
                  Certificate.outside)
                Certificate.outside)
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
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)))
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))
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
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.cross (-346754670756747637 : ℤ) (731834939447705600 : ℕ) none)
                        (Certificate.splitY (-432 : ℤ)
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-44310282614342121697 : ℤ) (79263353441720729600 : ℕ) none)
                            (Certificate.cross (-573257524117118399 : ℤ) (900719925474099200 : ℕ) none))
                          (Certificate.cross (-1835048312408045923 : ℤ) (2927339757790822400 : ℕ) none))))))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.cross (-1136271759970538399 : ℤ) (2026619832316723200 : ℕ) none)
                      (Certificate.cross (-354446658631085753 : ℤ) (534802455750246400 : ℕ) none))
                    (Certificate.cross (-340235241737761003 : ℤ) (534802455750246400 : ℕ) none))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (-160265850998218439 : ℤ) (408138716230451200 : ℕ) none)
                    (Certificate.cross (-2107889809750519 : ℤ) (3518437208883200 : ℕ) none))
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-5299059113425751 : ℤ) (9675702324428800 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (456 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
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
                Certificate.outside
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
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
            Certificate.inside
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            Certificate.inside)
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
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-312 : ℤ)
                            Certificate.inside
                            Certificate.inside)))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-11311107755527631 : ℤ) (253327479039590400 : ℕ) none)
                        (Certificate.cross (-2796028244833379 : ℤ) (10555311626649600 : ℕ) none)))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.cross (-550598721807654221 : ℤ) (4053239664633446400 : ℕ) none)
                        (Certificate.cross (-2796028244833379 : ℤ) (10555311626649600 : ℕ) none))))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                            (Certificate.cross (-3531394986585230009 : ℤ) (16212958658533785600 : ℕ) none)))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (-5287580947124524663 : ℤ) (86469112845513523200 : ℕ) none)
                            (Certificate.cross (-3531394986585230009 : ℤ) (16212958658533785600 : ℕ) none))
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.splitY (-120 : ℤ)
                              (Certificate.cross (-238410554248040192201 : ℤ) (1037629354146162278400 : ℕ) none)
                              Certificate.outside)
                            Certificate.outside)))
                      (Certificate.cross (-65958799203180907 : ℤ) (189995609279692800 : ℕ) none))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.cross (-65958799203180907 : ℤ) (189995609279692800 : ℕ) none)
                      Certificate.outside)))))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.inside
              Certificate.inside)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-432 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-2423890315094562221 : ℤ) (4053239664633446400 : ℕ) none))
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (-468263300259828149 : ℤ) (1013309916158361600 : ℕ) none)
                          (Certificate.cross (-961949852325884649 : ℤ) (1576259869579673600 : ℕ) none)))))
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.cross (-333824959101528387 : ℤ) (788129934789836800 : ℕ) none)
                    (Certificate.cross (-18177544009900129 : ℤ) (28147497671065600 : ℕ) none))))
              (Certificate.cross (-338338673581009 : ℤ) (659706976665600 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-125650463433103753 : ℤ) (337769972052787200 : ℕ) none)
                      (Certificate.cross (-25261299113234141 : ℤ) (42221246506598400 : ℕ) none))
                    (Certificate.cross (-1663956894094485637 : ℤ) (3039929748475084800 : ℕ) none))
                  Certificate.outside)
                Certificate.outside)
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
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)))
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))
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
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.cross (-468263300259828149 : ℤ) (1013309916158361600 : ℕ) none)
                        (Certificate.splitY (-432 : ℤ)
                          (Certificate.cross (-2423890315094562221 : ℤ) (4053239664633446400 : ℕ) none)
                          (Certificate.cross (-961949852325884649 : ℤ) (1576259869579673600 : ℕ) none))))))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.cross (-1208343938524238673 : ℤ) (3152519739159347200 : ℕ) none)
                      (Certificate.cross (-2236543549821793 : ℤ) (3518437208883200 : ℕ) none))
                    (Certificate.cross (-467350244778433753 : ℤ) (759982437118771200 : ℕ) none))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (-1243873970161469887 : ℤ) (3039929748475084800 : ℕ) none)
                    (Certificate.cross (-25261299113234141 : ℤ) (42221246506598400 : ℕ) none))
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-338338673581009 : ℤ) (659706976665600 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (456 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
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
                Certificate.outside
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
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
            Certificate.inside
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            Certificate.inside)
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
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.cross (-145778893397219 : ℤ) (549755813888000 : ℕ) none)))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.cross (-39550678106535673 : ℤ) (1125899906842624000 : ℕ) none)
                        (Certificate.cross (-145778893397219 : ℤ) (549755813888000 : ℕ) none))))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-917019292429263817 : ℤ) (4503599627370496000 : ℕ) none))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-917019292429263817 : ℤ) (4503599627370496000 : ℕ) none)
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.splitY (-120 : ℤ)
                              (Certificate.cross (-65656468375884438913 : ℤ) (288230376151711744000 : ℕ) none)
                              (Certificate.cross (-24081733686201931661 : ℤ) (90071992547409920000 : ℕ) none))
                            (Certificate.cross (-328601470485414637 : ℤ) (1125899906842624000 : ℕ) none))))
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-5057513265279947317 : ℤ) (18014398509481984000 : ℕ) none)
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-5057513265279947317 : ℤ) (18014398509481984000 : ℕ) none)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-432 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-693547571307776173 : ℤ) (1125899906842624000 : ℕ) none))
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (-56620171041913631 : ℤ) (140737488355328000 : ℕ) none)
                          (Certificate.cross (-178486327030302381 : ℤ) (281474976710656000 : ℕ) none)))))
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.cross (-11514563440213883 : ℤ) (26388279066624000 : ℕ) none)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-432 : ℤ)
                        (Certificate.cross (-267492565371191881 : ℤ) (422212465065984000 : ℕ) none)
                        Certificate.outside)
                      Certificate.outside))))
              (Certificate.cross (-4676058542235251 : ℤ) (8796093022208000 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-832828597537301399 : ℤ) (2251799813685248000 : ℕ) none)
                      (Certificate.cross (-2716817510388877 : ℤ) (4398046511104000 : ℕ) none))
                    (Certificate.cross (-791841592081882631 : ℤ) (1407374883553280000 : ℕ) none))
                  Certificate.outside)
                Certificate.outside)
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
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)))
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))
                  Certificate.outside))))
          Certificate.outside)),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
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
                        (Certificate.cross (-56620171041913631 : ℤ) (140737488355328000 : ℕ) none)
                        (Certificate.splitY (-432 : ℤ)
                          (Certificate.cross (-693547571307776173 : ℤ) (1125899906842624000 : ℕ) none)
                          (Certificate.cross (-178486327030302381 : ℤ) (281474976710656000 : ℕ) none))))))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.cross (-381297232781364399 : ℤ) (1125899906842624000 : ℕ) none)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-432 : ℤ)
                          (Certificate.cross (-34047264641373219143 : ℤ) (54043195528445952000 : ℕ) none)
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.cross (-111683669451330157 : ℤ) (175921860444160000 : ℕ) none))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (-296746234641340003 : ℤ) (703687441776640000 : ℕ) none)
                    (Certificate.cross (-2716817510388877 : ℤ) (4398046511104000 : ℕ) none))
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-4676058542235251 : ℤ) (8796093022208000 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (456 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
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
                Certificate.outside
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
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
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

end BerryEsseen.N2NeededIntegerPointwise04

#print axioms BerryEsseen.N2NeededIntegerPointwise04.powers_entries
#print axioms BerryEsseen.N2NeededIntegerPointwise04.powers_eq
#print axioms BerryEsseen.N2NeededIntegerPointwise04.checks
#print axioms BerryEsseen.N2NeededIntegerPointwise04.pointwise
