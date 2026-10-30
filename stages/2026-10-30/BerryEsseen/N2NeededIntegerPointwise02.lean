module

public import BerryEsseen.N2NeededIntegerData
public import BerryEsseen.N2IntegerPointwiseReplay

@[expose] public section

/-! 2026-10-29: integer power numerators and the unchanged original
rows015..019 closed trees. The entries equality is the semantic cache bridge.
No Bernstein coefficient or host closed flag is a premise. -/

namespace BerryEsseen.N2NeededIntegerPointwise02

open N2NeededData N2NeededIntegerData N2IntegerBernstein
  N2IntegerRectangleCertificate N2MajorantPolynomials

def rowIndex (j : Fin 5) : Fin 65 :=
  ⟨2 * 5 + j.val,
    lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (2 * 5)) (by decide)⟩

def signX : Fin 4 → ℚ := N2IntegerPointwiseReplay.signX
def signY : Fin 4 → ℚ := N2IntegerPointwiseReplay.signY

def powers : Fin 5 → Fin 4 → IntPower :=
  ![
    ![
      ![![(58831990448289 : ℤ), (-103185457330375 : ℤ), (72780604656750 : ℤ), (-48369137877625 : ℤ)],
        ![(-103185457330375 : ℤ), (199501257680500 : ℤ), (-104831570785875 : ℤ), (-32617369529375 : ℤ)],
        ![(72780604656750 : ℤ), (-104831570785875 : ℤ), (-44249192858875 : ℤ), (105401989183500 : ℤ)],
        ![(-48369137877625 : ℤ), (-32617369529375 : ℤ), (105401989183500 : ℤ), (80518603831000 : ℤ)]],
      ![![(58831990448289 : ℤ), (-103185457330375 : ℤ), (72780604656750 : ℤ), (-9431845083875 : ℤ)],
        ![(-103185457330375 : ℤ), (199501257680500 : ℤ), (-104831570785875 : ℤ), (15401075312125 : ℤ)],
        ![(72780604656750 : ℤ), (-104831570785875 : ℤ), (-44249192858875 : ℤ), (28331239785250 : ℤ)],
        ![(-48369137877625 : ℤ), (-32617369529375 : ℤ), (105401989183500 : ℤ), (-72243020331250 : ℤ)]],
      ![![(58831990448289 : ℤ), (-103185457330375 : ℤ), (72780604656750 : ℤ), (-48369137877625 : ℤ)],
        ![(-103185457330375 : ℤ), (199501257680500 : ℤ), (-104831570785875 : ℤ), (-32617369529375 : ℤ)],
        ![(72780604656750 : ℤ), (-104831570785875 : ℤ), (-44249192858875 : ℤ), (105401989183500 : ℤ)],
        ![(-9431845083875 : ℤ), (15401075312125 : ℤ), (28331239785250 : ℤ), (-72243020331250 : ℤ)]],
      ![![(58831990448289 : ℤ), (-103185457330375 : ℤ), (72780604656750 : ℤ), (-9431845083875 : ℤ)],
        ![(-103185457330375 : ℤ), (199501257680500 : ℤ), (-104831570785875 : ℤ), (15401075312125 : ℤ)],
        ![(72780604656750 : ℤ), (-104831570785875 : ℤ), (-44249192858875 : ℤ), (28331239785250 : ℤ)],
        ![(-9431845083875 : ℤ), (15401075312125 : ℤ), (28331239785250 : ℤ), (-8253161111000 : ℤ)]]],
    ![
      ![![(50674196144789 : ℤ), (-121190963895500 : ℤ), (99317609944000 : ℤ), (-42116501718500 : ℤ)],
        ![(-121190963895500 : ℤ), (197337466237000 : ℤ), (-85478242940375 : ℤ), (-23466638684625 : ℤ)],
        ![(99317609944000 : ℤ), (-85478242940375 : ℤ), (-88902539129375 : ℤ), (94588714198625 : ℤ)],
        ![(-42116501718500 : ℤ), (-23466638684625 : ℤ), (94588714198625 : ℤ), (72953199135000 : ℤ)]],
      ![![(50674196144789 : ℤ), (-121190963895500 : ℤ), (99317609944000 : ℤ), (-13318481013250 : ℤ)],
        ![(-121190963895500 : ℤ), (197337466237000 : ℤ), (-85478242940375 : ℤ), (12288383144625 : ℤ)],
        ![(99317609944000 : ℤ), (-85478242940375 : ℤ), (-88902539129375 : ℤ), (34967250104625 : ℤ)],
        ![(-42116501718500 : ℤ), (-23466638684625 : ℤ), (94588714198625 : ℤ), (-75176505604500 : ℤ)]],
      ![![(50674196144789 : ℤ), (-121190963895500 : ℤ), (99317609944000 : ℤ), (-42116501718500 : ℤ)],
        ![(-121190963895500 : ℤ), (197337466237000 : ℤ), (-85478242940375 : ℤ), (-23466638684625 : ℤ)],
        ![(99317609944000 : ℤ), (-85478242940375 : ℤ), (-88902539129375 : ℤ), (94588714198625 : ℤ)],
        ![(-13318481013250 : ℤ), (12288383144625 : ℤ), (34967250104625 : ℤ), (-75176505604500 : ℤ)]],
      ![![(50674196144789 : ℤ), (-121190963895500 : ℤ), (99317609944000 : ℤ), (-13318481013250 : ℤ)],
        ![(-121190963895500 : ℤ), (197337466237000 : ℤ), (-85478242940375 : ℤ), (12288383144625 : ℤ)],
        ![(99317609944000 : ℤ), (-85478242940375 : ℤ), (-88902539129375 : ℤ), (34967250104625 : ℤ)],
        ![(-13318481013250 : ℤ), (12288383144625 : ℤ), (34967250104625 : ℤ), (-9229553269500 : ℤ)]]],
    ![
      ![![(61711861461539 : ℤ), (-138680920525000 : ℤ), (101658413217250 : ℤ), (-38331974534625 : ℤ)],
        ![(-138680920525000 : ℤ), (213296204632125 : ℤ), (-71298947401375 : ℤ), (-33450348506375 : ℤ)],
        ![(101658413217250 : ℤ), (-71298947401375 : ℤ), (-102738323282625 : ℤ), (100040211864000 : ℤ)],
        ![(-38331974534625 : ℤ), (-33450348506375 : ℤ), (100040211864000 : ℤ), (91384273694125 : ℤ)]],
      ![![(61711861461539 : ℤ), (-138680920525000 : ℤ), (101658413217250 : ℤ), (-12779472232875 : ℤ)],
        ![(-138680920525000 : ℤ), (213296204632125 : ℤ), (-71298947401375 : ℤ), (-847916984625 : ℤ)],
        ![(101658413217250 : ℤ), (-71298947401375 : ℤ), (-102738323282625 : ℤ), (42661555747250 : ℤ)],
        ![(-38331974534625 : ℤ), (-33450348506375 : ℤ), (100040211864000 : ℤ), (-71697233907125 : ℤ)]],
      ![![(61711861461539 : ℤ), (-138680920525000 : ℤ), (101658413217250 : ℤ), (-38331974534625 : ℤ)],
        ![(-138680920525000 : ℤ), (213296204632125 : ℤ), (-71298947401375 : ℤ), (-33450348506375 : ℤ)],
        ![(101658413217250 : ℤ), (-71298947401375 : ℤ), (-102738323282625 : ℤ), (100040211864000 : ℤ)],
        ![(-12779472232875 : ℤ), (-847916984625 : ℤ), (42661555747250 : ℤ), (-71697233907125 : ℤ)]],
      ![![(61711861461539 : ℤ), (-138680920525000 : ℤ), (101658413217250 : ℤ), (-12779472232875 : ℤ)],
        ![(-138680920525000 : ℤ), (213296204632125 : ℤ), (-71298947401375 : ℤ), (-847916984625 : ℤ)],
        ![(101658413217250 : ℤ), (-71298947401375 : ℤ), (-102738323282625 : ℤ), (42661555747250 : ℤ)],
        ![(-12779472232875 : ℤ), (-847916984625 : ℤ), (42661555747250 : ℤ), (-10828144945375 : ℤ)]]],
    ![
      ![![(88955819833039 : ℤ), (-160771317512375 : ℤ), (115006440960250 : ℤ), (-8264890663125 : ℤ)],
        ![(-160771317512375 : ℤ), (208362077546250 : ℤ), (-16804721682125 : ℤ), (-8332782249875 : ℤ)],
        ![(115006440960250 : ℤ), (-16804721682125 : ℤ), (-247110631358875 : ℤ), (-40937370813250 : ℤ)],
        ![(-8264890663125 : ℤ), (-8332782249875 : ℤ), (-40937370813250 : ℤ), (-5910470341250 : ℤ)]],
      ![![(88955819833039 : ℤ), (-160771317512375 : ℤ), (115006440960250 : ℤ), (-13072455094125 : ℤ)],
        ![(-160771317512375 : ℤ), (208362077546250 : ℤ), (-16804721682125 : ℤ), (-21371186798125 : ℤ)],
        ![(115006440960250 : ℤ), (-16804721682125 : ℤ), (-247110631358875 : ℤ), (87622603105500 : ℤ)],
        ![(-8264890663125 : ℤ), (-8332782249875 : ℤ), (-40937370813250 : ℤ), (-19946342714000 : ℤ)]],
      ![![(88955819833039 : ℤ), (-160771317512375 : ℤ), (115006440960250 : ℤ), (-8264890663125 : ℤ)],
        ![(-160771317512375 : ℤ), (208362077546250 : ℤ), (-16804721682125 : ℤ), (-8332782249875 : ℤ)],
        ![(115006440960250 : ℤ), (-16804721682125 : ℤ), (-247110631358875 : ℤ), (-40937370813250 : ℤ)],
        ![(-13072455094125 : ℤ), (-21371186798125 : ℤ), (87622603105500 : ℤ), (-19946342714000 : ℤ)]],
      ![![(88955819833039 : ℤ), (-160771317512375 : ℤ), (115006440960250 : ℤ), (-13072455094125 : ℤ)],
        ![(-160771317512375 : ℤ), (208362077546250 : ℤ), (-16804721682125 : ℤ), (-21371186798125 : ℤ)],
        ![(115006440960250 : ℤ), (-16804721682125 : ℤ), (-247110631358875 : ℤ), (87622603105500 : ℤ)],
        ![(-13072455094125 : ℤ), (-21371186798125 : ℤ), (87622603105500 : ℤ), (-21178194401250 : ℤ)]]],
    ![
      ![![(98836678394664 : ℤ), (-166123283156500 : ℤ), (105624097509875 : ℤ), (-11397383302500 : ℤ)],
        ![(-166123283156500 : ℤ), (222276201172000 : ℤ), (-36912093086250 : ℤ), (-27862570276875 : ℤ)],
        ![(105624097509875 : ℤ), (-36912093086250 : ℤ), (-186730178804000 : ℤ), (26166585556875 : ℤ)],
        ![(-11397383302500 : ℤ), (-27862570276875 : ℤ), (26166585556875 : ℤ), (44377096973375 : ℤ)]],
      ![![(98836678394664 : ℤ), (-166123283156500 : ℤ), (105624097509875 : ℤ), (-12155068410500 : ℤ)],
        ![(-166123283156500 : ℤ), (222276201172000 : ℤ), (-36912093086250 : ℤ), (-12658857807625 : ℤ)],
        ![(105624097509875 : ℤ), (-36912093086250 : ℤ), (-186730178804000 : ℤ), (67678904132625 : ℤ)],
        ![(-11397383302500 : ℤ), (-27862570276875 : ℤ), (26166585556875 : ℤ), (-54871414543875 : ℤ)]],
      ![![(98836678394664 : ℤ), (-166123283156500 : ℤ), (105624097509875 : ℤ), (-11397383302500 : ℤ)],
        ![(-166123283156500 : ℤ), (222276201172000 : ℤ), (-36912093086250 : ℤ), (-27862570276875 : ℤ)],
        ![(105624097509875 : ℤ), (-36912093086250 : ℤ), (-186730178804000 : ℤ), (26166585556875 : ℤ)],
        ![(-12155068410500 : ℤ), (-12658857807625 : ℤ), (67678904132625 : ℤ), (-54871414543875 : ℤ)]],
      ![![(98836678394664 : ℤ), (-166123283156500 : ℤ), (105624097509875 : ℤ), (-12155068410500 : ℤ)],
        ![(-166123283156500 : ℤ), (222276201172000 : ℤ), (-36912093086250 : ℤ), (-12658857807625 : ℤ)],
        ![(105624097509875 : ℤ), (-36912093086250 : ℤ), (-186730178804000 : ℤ), (67678904132625 : ℤ)],
        ![(-12155068410500 : ℤ), (-12658857807625 : ℤ), (67678904132625 : ℤ), (-16508955298625 : ℤ)]]]]

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
                          Certificate.inside
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (-312 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (-300 : ℤ)
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (-306 : ℤ)
                                      (Certificate.splitX (-1533 : ℤ)
                                        (Certificate.splitY (-309 : ℤ)
                                          Certificate.inside
                                          Certificate.inside)
                                        Certificate.inside)
                                      Certificate.inside)
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside))
                            (Certificate.splitY (-312 : ℤ)
                              Certificate.inside
                              Certificate.inside)))
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-1392 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-1056 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)))))
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
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (-300 : ℤ)
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (-306 : ℤ)
                                    (Certificate.splitY (-1530 : ℤ)
                                      (Certificate.splitX (-309 : ℤ)
                                        Certificate.inside
                                        Certificate.inside)
                                      Certificate.inside)
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside))
                          Certificate.inside))
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-960 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside)))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.cross (-73147493035813 : ℤ) (879609302220800 : ℕ) none))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-73147493035813 : ℤ) (879609302220800 : ℕ) none)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-60622568880480673 : ℤ) (225179981368524800 : ℕ) none)
                        (Certificate.cross (-42557692302645907 : ℤ) (56294995342131200 : ℕ) none))))
                  (Certificate.cross (-8012655921750961 : ℤ) (10555311626649600 : ℕ) none))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.cross (-8012655921750961 : ℤ) (10555311626649600 : ℕ) none)
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
                  (Certificate.cross (-228222635609863753 : ℤ) (225179981368524800 : ℕ) none)
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.cross (-4071885215663283881 : ℤ) (7205759403792793600 : ℕ) none)))
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-624 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-648 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              (Certificate.cross (-3665438006438169839557 : ℤ) (3689348814741910323200 : ℕ) none)
                              (Certificate.splitX (-660 : ℤ)
                                (Certificate.cross (-6114287337007776052163 : ℤ) (5534023222112865484800 : ℕ) none)
                                (Certificate.splitY (228 : ℤ)
                                  (Certificate.cross (-62852206904440056289853 : ℤ) (51650883406386744524800 : ℕ) none)
                                  Certificate.outside)))
                            (Certificate.splitY (216 : ℤ)
                              (Certificate.cross (-2217371371846737335911 : ℤ) (1844674407370955161600 : ℕ) none)
                              Certificate.outside))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-29463687756094521 : ℤ) (28147497671065600 : ℕ) none)
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
                      Certificate.outside)
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              Certificate.outside
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (1344 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-48 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-24 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-12 : ℤ)
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (-18 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))
                                Certificate.outside))))))))))))),
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
                  (Certificate.cross (-228222635609863753 : ℤ) (225179981368524800 : ℕ) none)
                  (Certificate.cross (-29463687756094521 : ℤ) (28147497671065600 : ℕ) none))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.cross (-4071885215663283881 : ℤ) (7205759403792793600 : ℕ) none))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-624 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.cross (-989935380080865887777 : ℤ) (807045053224792883200 : ℕ) none)
                            (Certificate.splitY (-648 : ℤ)
                              (Certificate.splitX (228 : ℤ)
                                (Certificate.cross (-62852206904440056289853 : ℤ) (51650883406386744524800 : ℕ) none)
                                (Certificate.cross (-165542041960293304250831 : ℤ) (140195254960192592281600 : ℕ) none))
                              Certificate.outside))
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.cross (-170087714915977213 : ℤ) (225179981368524800 : ℕ) none))
                  Certificate.outside))
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)))
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    Certificate.outside))))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            Certificate.outside
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                Certificate.outside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-24 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-12 : ℤ)
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (-18 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))
                                  Certificate.outside)))))))))))))),
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
        Certificate.outside)],
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
                                  Certificate.inside
                                  Certificate.inside)
                                (Certificate.splitY (-324 : ℤ)
                                  Certificate.inside
                                  Certificate.inside))
                              Certificate.inside)
                            (Certificate.splitY (-312 : ℤ)
                              (Certificate.splitX (-1500 : ℤ)
                                (Certificate.splitY (-324 : ℤ)
                                  Certificate.inside
                                  Certificate.inside)
                                (Certificate.splitY (-324 : ℤ)
                                  Certificate.inside
                                  Certificate.inside))
                              Certificate.inside)))
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1464 : ℤ)
                            (Certificate.splitY (-312 : ℤ)
                              (Certificate.splitX (-1476 : ℤ)
                                (Certificate.splitY (-324 : ℤ)
                                  Certificate.inside
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside)
                            (Certificate.splitY (-312 : ℤ)
                              Certificate.inside
                              Certificate.inside))))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-1392 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1416 : ℤ)
                            (Certificate.splitY (-312 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside))
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-1296 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-1200 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside))
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                Certificate.inside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-816 : ℤ)
                        (Certificate.splitY (-432 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-432 : ℤ)
                          Certificate.inside
                          Certificate.inside))))))
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-1056 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-1104 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-1008 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside))
                  Certificate.inside)
                Certificate.inside))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-960 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-864 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-432 : ℤ)
                        Certificate.inside
                        Certificate.inside))))))
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
                                Certificate.inside
                                Certificate.inside)
                              (Certificate.splitX (-324 : ℤ)
                                Certificate.inside
                                Certificate.inside))
                            Certificate.inside)
                          (Certificate.splitX (-312 : ℤ)
                            (Certificate.splitY (-1464 : ℤ)
                              (Certificate.splitX (-324 : ℤ)
                                Certificate.inside
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)))
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1392 : ℤ)
                          (Certificate.splitX (-312 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          Certificate.inside)))
                    Certificate.inside)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-1248 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-960 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-1056 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside)))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.splitY (-432 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-432 : ℤ)
                          Certificate.inside
                          Certificate.inside)))
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.splitX (-624 : ℤ)
                        (Certificate.splitY (-528 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-528 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-600 : ℤ)
                            (Certificate.splitY (-504 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (-504 : ℤ)
                              Certificate.inside
                              Certificate.inside))))
                      (Certificate.splitX (-624 : ℤ)
                        (Certificate.splitY (-432 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside))))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-528 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-624 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-504 : ℤ)
                            (Certificate.splitY (-600 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside))))
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (-432 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      (Certificate.splitX (-432 : ℤ)
                        Certificate.inside
                        Certificate.inside)))
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.splitX (-528 : ℤ)
                        (Certificate.splitY (-528 : ℤ)
                          (Certificate.splitX (-552 : ℤ)
                            (Certificate.splitY (-552 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-564 : ℤ)
                                Certificate.inside
                                Certificate.inside))
                            (Certificate.splitY (-552 : ℤ)
                              (Certificate.splitX (-540 : ℤ)
                                Certificate.inside
                                Certificate.inside)
                              Certificate.inside))
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-5272777378002047 : ℤ) (7036874417766400 : ℕ) none)))))
                  (Certificate.cross (-171092655650114189 : ℤ) (225179981368524800 : ℕ) none))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.cross (-171092655650114189 : ℤ) (225179981368524800 : ℕ) none)
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
                  (Certificate.cross (-23334207696667313 : ℤ) (28147497671065600 : ℕ) none)
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-720 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-624 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-648 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-1087590449199417024929 : ℤ) (922337203685477580800 : ℕ) none))
                            (Certificate.splitY (216 : ℤ)
                              (Certificate.cross (-368753393880562445009 : ℤ) (345876451382054092800 : ℕ) none)
                              (Certificate.splitX (-636 : ℤ)
                                (Certificate.splitY (228 : ℤ)
                                  (Certificate.cross (-222734145412212674394287 : ℤ) (191846138366579336806400 : ℕ) none)
                                  Certificate.outside)
                                Certificate.outside)))
                          (Certificate.cross (-127118354586693340673 : ℤ) (115292150460684697600 : ℕ) none))
                        (Certificate.cross (-10136841468205848317 : ℤ) (6305039478318694400 : ℕ) none))
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-222686783334839939 : ℤ) (225179981368524800 : ℕ) none)
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
                      Certificate.outside
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
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
                          Certificate.outside)
                        Certificate.outside))
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              Certificate.outside
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (1344 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-48 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-24 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-12 : ℤ)
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (-18 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))
                                Certificate.outside))))))))))))),
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
                  (Certificate.cross (-23334207696667313 : ℤ) (28147497671065600 : ℕ) none)
                  (Certificate.cross (-222686783334839939 : ℤ) (225179981368524800 : ℕ) none))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-624 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.cross (-368753393880562445009 : ℤ) (345876451382054092800 : ℕ) none)
                            (Certificate.splitY (-648 : ℤ)
                              (Certificate.cross (-1087590449199417024929 : ℤ) (922337203685477580800 : ℕ) none)
                              (Certificate.splitX (228 : ℤ)
                                (Certificate.cross (-9770111099413424571841 : ℤ) (8301034833169298227200 : ℕ) none)
                                Certificate.outside)))
                          (Certificate.cross (-4124302730223266971 : ℤ) (3152519739159347200 : ℕ) none))
                        (Certificate.cross (-1829132746438358423 : ℤ) (1576259869579673600 : ℕ) none)))
                    (Certificate.cross (-37035835894870719 : ℤ) (49258120924364800 : ℕ) none))
                  Certificate.outside))
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)))
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)))))
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
            Certificate.outside
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                Certificate.outside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1440 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-24 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-12 : ℤ)
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (-18 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))
                                  Certificate.outside)))))))))))))),
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
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        Certificate.outside)))))
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
          Certificate.outside)
        Certificate.outside)],
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
                      Certificate.inside
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (-264 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (-276 : ℤ)
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (-282 : ℤ)
                                      Certificate.inside
                                      (Certificate.splitX (-1533 : ℤ)
                                        (Certificate.splitY (-279 : ℤ)
                                          Certificate.inside
                                          Certificate.inside)
                                        Certificate.inside))
                                    Certificate.inside)
                                  Certificate.inside)
                                (Certificate.splitY (-276 : ℤ)
                                  Certificate.inside
                                  Certificate.inside))
                              Certificate.inside)
                            (Certificate.splitY (-264 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (-1464 : ℤ)
                            (Certificate.splitY (-264 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside)))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-1056 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (-264 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (-276 : ℤ)
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (-282 : ℤ)
                                    Certificate.inside
                                    (Certificate.splitY (-1530 : ℤ)
                                      (Certificate.splitX (-279 : ℤ)
                                        Certificate.inside
                                        Certificate.inside)
                                      Certificate.inside))
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)
                          (Certificate.splitX (-264 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        Certificate.inside)
                      Certificate.inside))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-960 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                (Certificate.cross (0 : ℤ) (1 : ℕ) none))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-155922770288269131 : ℤ) (225179981368524800 : ℕ) none)))))
                  (Certificate.cross (-35332434539911141 : ℤ) (49258120924364800 : ℕ) none))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.cross (-35332434539911141 : ℤ) (49258120924364800 : ℕ) none)
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
                  (Certificate.cross (-117543672198565881 : ℤ) (225179981368524800 : ℕ) none)
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-720 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-624 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-648 : ℤ)
                            (Certificate.cross (-246695132581900727733 : ℤ) (461168601842738790400 : ℕ) none)
                            (Certificate.splitY (216 : ℤ)
                              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                              (Certificate.splitX (-636 : ℤ)
                                (Certificate.splitY (228 : ℤ)
                                  (Certificate.cross (-160878115592484098627421 : ℤ) (236118324143482260684800 : ℕ) none)
                                  (Certificate.cross (-104456887928148229221581 : ℤ) (88544371553805847756800 : ℕ) none))
                                (Certificate.cross (-32992396111622874238103 : ℤ) (25825441703193372262400 : ℕ) none))))
                          (Certificate.cross (-201622929246971115913 : ℤ) (172938225691027046400 : ℕ) none))
                        (Certificate.cross (-21530990428679348893 : ℤ) (10808639105689190400 : ℕ) none))
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-378701295514245503 : ℤ) (394064967394918400 : ℕ) none)
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
                      Certificate.outside
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
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
                          Certificate.outside)
                        Certificate.outside))
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)))
          Certificate.outside)),
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
                  (Certificate.cross (-117543672198565881 : ℤ) (225179981368524800 : ℕ) none)
                  (Certificate.cross (-378701295514245503 : ℤ) (394064967394918400 : ℕ) none))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-624 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                            (Certificate.splitY (-648 : ℤ)
                              (Certificate.cross (-246695132581900727733 : ℤ) (461168601842738790400 : ℕ) none)
                              (Certificate.splitX (228 : ℤ)
                                (Certificate.cross (-35590095478888229137989 : ℤ) (31359464925306237747200 : ℕ) none)
                                (Certificate.cross (-4675982848613813982483 : ℤ) (3919933115663279718400 : ℕ) none))))
                          (Certificate.cross (-118245127228132994519 : ℤ) (86469112845513523200 : ℕ) none))
                        (Certificate.cross (-28905293467954825661 : ℤ) (21617278211378380800 : ℕ) none)))
                    (Certificate.cross (-6947623850448709923 : ℤ) (8556839292003942400 : ℕ) none))
                  Certificate.outside))
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
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
                        Certificate.outside)
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside))))
        (Certificate.cross (-83551686333459 : ℤ) (632219185971200 : ℕ) none)),
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
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside))))
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
                  Certificate.outside
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (24 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (36 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (42 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))))))
                        Certificate.outside))
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
                        (Certificate.splitY (48 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (24 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (36 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (42 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))))))
                          Certificate.outside))
                      Certificate.outside))
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
              (Certificate.splitX (-960 : ℤ)
                Certificate.inside
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
              Certificate.inside
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
                          (Certificate.splitX (-744 : ℤ)
                            (Certificate.splitY (-744 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (-744 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside)
                        (Certificate.splitY (-720 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-34790873913551753 : ℤ) (56294995342131200 : ℕ) none)))
                  (Certificate.cross (-18679625440819719 : ℤ) (28147497671065600 : ℕ) none))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.cross (-18679625440819719 : ℤ) (28147497671065600 : ℕ) none)
                  Certificate.outside)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.inside
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                Certificate.inside
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
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                  (Certificate.cross (-6709019539410469 : ℤ) (28147497671065600 : ℕ) none))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-63550826257847141 : ℤ) (77405618595430400 : ℕ) none)
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
                          Certificate.outside)
                        Certificate.outside))
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)))
          Certificate.outside)),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              Certificate.inside
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                  (Certificate.cross (-63550826257847141 : ℤ) (77405618595430400 : ℕ) none))
                (Certificate.cross (-3513062828797043 : ℤ) (3518437208883200 : ℕ) none))
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside))))
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside))))
        (Certificate.cross (-20077866576247 : ℤ) (192414534860800 : ℕ) none)),
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
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
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
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (60 : ℤ)
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (54 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))
                                Certificate.outside))
                            Certificate.outside))))
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
                        (Certificate.splitY (48 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (48 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (72 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (60 : ℤ)
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (54 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))
                                  Certificate.outside))
                              Certificate.outside))))
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
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (-264 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (-276 : ℤ)
                                  Certificate.inside
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (-270 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside))
                                (Certificate.splitY (-276 : ℤ)
                                  Certificate.inside
                                  Certificate.inside))
                              Certificate.inside)
                            (Certificate.splitY (-264 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (-1464 : ℤ)
                            (Certificate.splitY (-264 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (-264 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside)))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1392 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside)))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-1056 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (-264 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (-276 : ℤ)
                                Certificate.inside
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (-270 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside))
                              Certificate.inside)
                            Certificate.inside)
                          (Certificate.splitX (-264 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        Certificate.inside)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        Certificate.inside)))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-960 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-624 : ℤ)
                        (Certificate.splitY (-432 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-432 : ℤ)
                          Certificate.inside
                          Certificate.inside)))))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-672 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-432 : ℤ)
                        (Certificate.splitY (-624 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside)))
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.splitX (-528 : ℤ)
                        (Certificate.splitY (-528 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-552 : ℤ)
                            (Certificate.splitY (-504 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (-504 : ℤ)
                              Certificate.inside
                              Certificate.inside)))
                        (Certificate.splitY (-528 : ℤ)
                          (Certificate.splitX (-504 : ℤ)
                            (Certificate.splitY (-552 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside))
                      Certificate.inside)
                    Certificate.inside)))
              Certificate.inside)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.cross (-45221147150252641 : ℤ) (70368744177664000 : ℕ) none))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.cross (-45221147150252641 : ℤ) (70368744177664000 : ℕ) none)
                  (Certificate.cross (-1514091846980313 : ℤ) (2199023255552000 : ℕ) none))))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                Certificate.inside
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside))
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
                  (Certificate.cross (-218912528636663253 : ℤ) (281474976710656000 : ℕ) none))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-528 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-552 : ℤ)
                            (Certificate.splitY (168 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-564 : ℤ)
                                (Certificate.cross (-1063608450634836101733 : ℤ) (1152921504606846976000 : ℕ) none)
                                (Certificate.cross (-2517068986487471888591 : ℤ) (2305843009213693952000 : ℕ) none)))
                            (Certificate.splitY (168 : ℤ)
                              (Certificate.cross (-9508428632762017609341 : ℤ) (9223372036854775808000 : ℕ) none)
                              (Certificate.cross (-2509548765391452096983 : ℤ) (2305843009213693952000 : ℕ) none))))
                        (Certificate.cross (-23734611599666926143 : ℤ) (18014398509481984000 : ℕ) none)))
                    (Certificate.cross (-656344360275918887 : ℤ) (562949953421312000 : ℕ) none))
                  (Certificate.cross (-317851215284086503 : ℤ) (281474976710656000 : ℕ) none)))
              (Certificate.cross (-17805904743644129 : ℤ) (52776558133248000 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-30085110360898883 : ℤ) (35184372088832000 : ℕ) none)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
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
                          Certificate.outside)
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
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
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
                    (Certificate.cross (-571502019358230131 : ℤ) (844424930131968000 : ℕ) none)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.cross (-186059083169940650947 : ℤ) (216172782113783808000 : ℕ) none)
                        (Certificate.splitY (-528 : ℤ)
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-605990596211761222277 : ℤ) (576460752303423488000 : ℕ) none)
                            (Certificate.splitY (-552 : ℤ)
                              (Certificate.splitX (180 : ℤ)
                                (Certificate.cross (-77829793261567472240581 : ℤ) (73786976294838206464000 : ℕ) none)
                                (Certificate.cross (-231087002620142920887037 : ℤ) (221360928884514619392000 : ℕ) none))
                              (Certificate.cross (-2509548765391452096983 : ℤ) (2305843009213693952000 : ℕ) none)))
                          (Certificate.cross (-78833562254170188661 : ℤ) (72057594037927936000 : ℕ) none)))
                      (Certificate.cross (-9172724053468127721 : ℤ) (9007199254740992000 : ℕ) none))))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.cross (-218912528636663253 : ℤ) (281474976710656000 : ℕ) none)
                  (Certificate.cross (-317851215284086503 : ℤ) (281474976710656000 : ℕ) none)))
              (Certificate.splitX (192 : ℤ)
                (Certificate.cross (-30085110360898883 : ℤ) (35184372088832000 : ℕ) none)
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
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-17805904743644129 : ℤ) (52776558133248000 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside))
                Certificate.outside))))
        (Certificate.cross (-326858954457461 : ℤ) (2473901162496000 : ℕ) none)),
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
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
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
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (60 : ℤ)
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (54 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))
                                Certificate.outside))
                            Certificate.outside))))
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
                        (Certificate.splitY (48 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (48 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (72 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (60 : ℤ)
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (54 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))
                                  Certificate.outside))
                              Certificate.outside))))
                      Certificate.outside))
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

end BerryEsseen.N2NeededIntegerPointwise02

#print axioms BerryEsseen.N2NeededIntegerPointwise02.powers_entries
#print axioms BerryEsseen.N2NeededIntegerPointwise02.powers_eq
#print axioms BerryEsseen.N2NeededIntegerPointwise02.checks
#print axioms BerryEsseen.N2NeededIntegerPointwise02.pointwise
