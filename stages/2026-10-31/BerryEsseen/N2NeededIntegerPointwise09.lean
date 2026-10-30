module

public import BerryEsseen.N2NeededIntegerData
public import BerryEsseen.N2IntegerPointwiseReplay

@[expose] public section

/-! 2026-10-29: integer power numerators and the unchanged original
rows050..054 closed trees. The entries equality is the semantic cache bridge.
No Bernstein coefficient or host closed flag is a premise. -/

namespace BerryEsseen.N2NeededIntegerPointwise09

open N2NeededData N2NeededIntegerData N2IntegerBernstein
  N2IntegerRectangleCertificate N2MajorantPolynomials

def rowIndex (j : Fin 5) : Fin 65 :=
  ⟨9 * 5 + j.val,
    lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (9 * 5)) (by decide)⟩

def signX : Fin 4 → ℚ := N2IntegerPointwiseReplay.signX
def signY : Fin 4 → ℚ := N2IntegerPointwiseReplay.signY

def powers : Fin 5 → Fin 4 → IntPower :=
  ![
    ![
      ![![(610682082620164 : ℤ), (-194854459294125 : ℤ), (-215141933742000 : ℤ), (-60333207562750 : ℤ)],
        ![(-194854459294125 : ℤ), (-258761248584875 : ℤ), (76544615592000 : ℤ), (79018649865000 : ℤ)],
        ![(-215141933742000 : ℤ), (76544615592000 : ℤ), (95353773481000 : ℤ), (-15299514669375 : ℤ)],
        ![(-60333207562750 : ℤ), (79018649865000 : ℤ), (-15299514669375 : ℤ), (-11508090301000 : ℤ)]],
      ![![(610682082620164 : ℤ), (-194854459294125 : ℤ), (-215141933742000 : ℤ), (83846985908250 : ℤ)],
        ![(-194854459294125 : ℤ), (-258761248584875 : ℤ), (76544615592000 : ℤ), (44421162672250 : ℤ)],
        ![(-215141933742000 : ℤ), (76544615592000 : ℤ), (95353773481000 : ℤ), (-12433949278625 : ℤ)],
        ![(-60333207562750 : ℤ), (79018649865000 : ℤ), (-15299514669375 : ℤ), (-4673475078500 : ℤ)]],
      ![![(610682082620164 : ℤ), (-194854459294125 : ℤ), (-215141933742000 : ℤ), (-60333207562750 : ℤ)],
        ![(-194854459294125 : ℤ), (-258761248584875 : ℤ), (76544615592000 : ℤ), (79018649865000 : ℤ)],
        ![(-215141933742000 : ℤ), (76544615592000 : ℤ), (95353773481000 : ℤ), (-15299514669375 : ℤ)],
        ![(83846985908250 : ℤ), (44421162672250 : ℤ), (-12433949278625 : ℤ), (-4673475078500 : ℤ)]],
      ![![(610682082620164 : ℤ), (-194854459294125 : ℤ), (-215141933742000 : ℤ), (83846985908250 : ℤ)],
        ![(-194854459294125 : ℤ), (-258761248584875 : ℤ), (76544615592000 : ℤ), (44421162672250 : ℤ)],
        ![(-215141933742000 : ℤ), (76544615592000 : ℤ), (95353773481000 : ℤ), (-12433949278625 : ℤ)],
        ![(83846985908250 : ℤ), (44421162672250 : ℤ), (-12433949278625 : ℤ), (-1888282147500 : ℤ)]]],
    ![
      ![![(629466162318164 : ℤ), (-169940938234375 : ℤ), (-227110910042375 : ℤ), (-64300260569875 : ℤ)],
        ![(-169940938234375 : ℤ), (-261103080431750 : ℤ), (46418664982375 : ℤ), (72904844408375 : ℤ)],
        ![(-227110910042375 : ℤ), (46418664982375 : ℤ), (108874235730250 : ℤ), (-8811710651750 : ℤ)],
        ![(-64300260569875 : ℤ), (72904844408375 : ℤ), (-8811710651750 : ℤ), (-9670794656500 : ℤ)]],
      ![![(629466162318164 : ℤ), (-169940938234375 : ℤ), (-227110910042375 : ℤ), (81640460936625 : ℤ)],
        ![(-169940938234375 : ℤ), (-261103080431750 : ℤ), (46418664982375 : ℤ), (51329488431875 : ℤ)],
        ![(-227110910042375 : ℤ), (46418664982375 : ℤ), (108874235730250 : ℤ), (-10510093482250 : ℤ)],
        ![(-64300260569875 : ℤ), (72904844408375 : ℤ), (-8811710651750 : ℤ), (-5375576757000 : ℤ)]],
      ![![(629466162318164 : ℤ), (-169940938234375 : ℤ), (-227110910042375 : ℤ), (-64300260569875 : ℤ)],
        ![(-169940938234375 : ℤ), (-261103080431750 : ℤ), (46418664982375 : ℤ), (72904844408375 : ℤ)],
        ![(-227110910042375 : ℤ), (46418664982375 : ℤ), (108874235730250 : ℤ), (-8811710651750 : ℤ)],
        ![(81640460936625 : ℤ), (51329488431875 : ℤ), (-10510093482250 : ℤ), (-5375576757000 : ℤ)]],
      ![![(629466162318164 : ℤ), (-169940938234375 : ℤ), (-227110910042375 : ℤ), (81640460936625 : ℤ)],
        ![(-169940938234375 : ℤ), (-261103080431750 : ℤ), (46418664982375 : ℤ), (51329488431875 : ℤ)],
        ![(-227110910042375 : ℤ), (46418664982375 : ℤ), (108874235730250 : ℤ), (-10510093482250 : ℤ)],
        ![(81640460936625 : ℤ), (51329488431875 : ℤ), (-10510093482250 : ℤ), (-2976089705500 : ℤ)]]],
    ![
      ![![(632877413977039 : ℤ), (-150991277086500 : ℤ), (-226303936742375 : ℤ), (-67012724363125 : ℤ)],
        ![(-150991277086500 : ℤ), (-263059837782375 : ℤ), (22621108211250 : ℤ), (67970538902750 : ℤ)],
        ![(-226303936742375 : ℤ), (22621108211250 : ℤ), (111743794756625 : ℤ), (-3574987439500 : ℤ)],
        ![(-67012724363125 : ℤ), (67970538902750 : ℤ), (-3574987439500 : ℤ), (-7971200011250 : ℤ)]],
      ![![(632877413977039 : ℤ), (-150991277086500 : ℤ), (-226303936742375 : ℤ), (77764683047625 : ℤ)],
        ![(-150991277086500 : ℤ), (-263059837782375 : ℤ), (22621108211250 : ℤ), (57017834283250 : ℤ)],
        ![(-226303936742375 : ℤ), (22621108211250 : ℤ), (111743794756625 : ℤ), (-6887170696750 : ℤ)],
        ![(-67012724363125 : ℤ), (67970538902750 : ℤ), (-3574987439500 : ℤ), (-5866090843000 : ℤ)]],
      ![![(632877413977039 : ℤ), (-150991277086500 : ℤ), (-226303936742375 : ℤ), (-67012724363125 : ℤ)],
        ![(-150991277086500 : ℤ), (-263059837782375 : ℤ), (22621108211250 : ℤ), (67970538902750 : ℤ)],
        ![(-226303936742375 : ℤ), (22621108211250 : ℤ), (111743794756625 : ℤ), (-3574987439500 : ℤ)],
        ![(77764683047625 : ℤ), (57017834283250 : ℤ), (-6887170696750 : ℤ), (-5866090843000 : ℤ)]],
      ![![(632877413977039 : ℤ), (-150991277086500 : ℤ), (-226303936742375 : ℤ), (77764683047625 : ℤ)],
        ![(-150991277086500 : ℤ), (-263059837782375 : ℤ), (22621108211250 : ℤ), (57017834283250 : ℤ)],
        ![(-226303936742375 : ℤ), (22621108211250 : ℤ), (111743794756625 : ℤ), (-6887170696750 : ℤ)],
        ![(77764683047625 : ℤ), (57017834283250 : ℤ), (-6887170696750 : ℤ), (-4327907725250 : ℤ)]]],
    ![
      ![![(636685715771289 : ℤ), (-134281465001000 : ℤ), (-216726090130750 : ℤ), (-67004776165625 : ℤ)],
        ![(-134281465001000 : ℤ), (-258630074467250 : ℤ), (4603445063250 : ℤ), (61943373085375 : ℤ)],
        ![(-216726090130750 : ℤ), (4603445063250 : ℤ), (95128046534625 : ℤ), (-2555208732125 : ℤ)],
        ![(-67004776165625 : ℤ), (61943373085375 : ℤ), (-2555208732125 : ℤ), (-7015621777000 : ℤ)]],
      ![![(636685715771289 : ℤ), (-134281465001000 : ℤ), (-216726090130750 : ℤ), (71502291510375 : ℤ)],
        ![(-134281465001000 : ℤ), (-258630074467250 : ℤ), (4603445063250 : ℤ), (58613481171375 : ℤ)],
        ![(-216726090130750 : ℤ), (4603445063250 : ℤ), (95128046534625 : ℤ), (53932453625 : ℤ)],
        ![(-67004776165625 : ℤ), (61943373085375 : ℤ), (-2555208732125 : ℤ), (-4558244644500 : ℤ)]],
      ![![(636685715771289 : ℤ), (-134281465001000 : ℤ), (-216726090130750 : ℤ), (-67004776165625 : ℤ)],
        ![(-134281465001000 : ℤ), (-258630074467250 : ℤ), (4603445063250 : ℤ), (61943373085375 : ℤ)],
        ![(-216726090130750 : ℤ), (4603445063250 : ℤ), (95128046534625 : ℤ), (-2555208732125 : ℤ)],
        ![(71502291510375 : ℤ), (58613481171375 : ℤ), (53932453625 : ℤ), (-4558244644500 : ℤ)]],
      ![![(636685715771289 : ℤ), (-134281465001000 : ℤ), (-216726090130750 : ℤ), (71502291510375 : ℤ)],
        ![(-134281465001000 : ℤ), (-258630074467250 : ℤ), (4603445063250 : ℤ), (58613481171375 : ℤ)],
        ![(-216726090130750 : ℤ), (4603445063250 : ℤ), (95128046534625 : ℤ), (53932453625 : ℤ)],
        ![(71502291510375 : ℤ), (58613481171375 : ℤ), (53932453625 : ℤ), (-6066470013000 : ℤ)]]],
    ![
      ![![(627329554304539 : ℤ), (-112635121732250 : ℤ), (-202776050702000 : ℤ), (-69074247731500 : ℤ)],
        ![(-112635121732250 : ℤ), (-254701003091125 : ℤ), (-22578630131250 : ℤ), (55753397728750 : ℤ)],
        ![(-202776050702000 : ℤ), (-22578630131250 : ℤ), (84617968629000 : ℤ), (3223547281625 : ℤ)],
        ![(-69074247731500 : ℤ), (55753397728750 : ℤ), (3223547281625 : ℤ), (-4743174818625 : ℤ)]],
      ![![(627329554304539 : ℤ), (-112635121732250 : ℤ), (-202776050702000 : ℤ), (64922313211750 : ℤ)],
        ![(-112635121732250 : ℤ), (-254701003091125 : ℤ), (-22578630131250 : ℤ), (64372000366750 : ℤ)],
        ![(-202776050702000 : ℤ), (-22578630131250 : ℤ), (84617968629000 : ℤ), (6013459211375 : ℤ)],
        ![(-69074247731500 : ℤ), (55753397728750 : ℤ), (3223547281625 : ℤ), (-6082946993625 : ℤ)]],
      ![![(627329554304539 : ℤ), (-112635121732250 : ℤ), (-202776050702000 : ℤ), (-69074247731500 : ℤ)],
        ![(-112635121732250 : ℤ), (-254701003091125 : ℤ), (-22578630131250 : ℤ), (55753397728750 : ℤ)],
        ![(-202776050702000 : ℤ), (-22578630131250 : ℤ), (84617968629000 : ℤ), (3223547281625 : ℤ)],
        ![(64922313211750 : ℤ), (64372000366750 : ℤ), (6013459211375 : ℤ), (-6082946993625 : ℤ)]],
      ![![(627329554304539 : ℤ), (-112635121732250 : ℤ), (-202776050702000 : ℤ), (64922313211750 : ℤ)],
        ![(-112635121732250 : ℤ), (-254701003091125 : ℤ), (-22578630131250 : ℤ), (64372000366750 : ℤ)],
        ![(-202776050702000 : ℤ), (-22578630131250 : ℤ), (84617968629000 : ℤ), (6013459211375 : ℤ)],
        ![(64922313211750 : ℤ), (64372000366750 : ℤ), (6013459211375 : ℤ), (-7798264920125 : ℤ)]]]]

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
        Certificate.inside
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
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
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (-264 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          Certificate.inside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          Certificate.inside))))
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
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (252 : ℤ)
                                  Certificate.inside
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)))
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1392 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      Certificate.inside))))
              Certificate.inside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                Certificate.inside)
              (Certificate.cross (-555486124467563 : ℤ) (6377167441100800 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-120675492230235503 : ℤ) (365917469723852800 : ℕ) none))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-264 : ℤ)
                            (Certificate.cross (-23772230512988295769 : ℤ) (100880631653099110400 : ℕ) none)
                            (Certificate.splitY (264 : ℤ)
                              (Certificate.cross (-280968311000606278277 : ℤ) (807045053224792883200 : ℕ) none)
                              (Certificate.cross (-16102193928976348643 : ℤ) (39631676720860364800 : ℕ) none))))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.cross (-264347067803426682527 : ℤ) (807045053224792883200 : ℕ) none)
                            (Certificate.cross (-961833145022846423 : ℤ) (2476979795053772800 : ℕ) none))
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.cross (-236311307135227329019 : ℤ) (533226195880666726400 : ℕ) none)
                            Certificate.outside)))
                      (Certificate.cross (-51080686517745391 : ℤ) (98516241848729600 : ℕ) none))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-64458493329125689 : ℤ) (182958734861926400 : ℕ) none))
                    (Certificate.cross (-781069560174911 : ℤ) (1759218604441600 : ℕ) none))
                  (Certificate.cross (-5875661006728501 : ℤ) (10555311626649600 : ℕ) none)))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.cross (-526544930535961 : ℤ) (934584883609600 : ℕ) none)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    Certificate.outside)))))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.cross (-986474353656797 : ℤ) (4343070929715200 : ℕ) none)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (864 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (816 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.splitY (840 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-228 : ℤ)
                                Certificate.outside
                                Certificate.outside))
                            (Certificate.splitY (840 : ℤ)
                              Certificate.outside
                              Certificate.outside))))
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (912 : ℤ)
                          (Certificate.splitX (-264 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          (Certificate.splitX (-264 : ℤ)
                            Certificate.outside
                            Certificate.outside))
                        (Certificate.splitY (912 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.splitY (888 : ℤ)
                              (Certificate.splitX (-228 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              Certificate.outside)
                            Certificate.outside)
                          Certificate.outside))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (1056 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (1056 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (1008 : ℤ)
                          (Certificate.splitX (-264 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (864 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (1248 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    Certificate.outside)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-360 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-372 : ℤ)
                                Certificate.outside
                                Certificate.outside))
                            Certificate.outside))
                        Certificate.outside))
                    Certificate.outside))
                Certificate.outside))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (252 : ℤ)
                                Certificate.inside
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside))
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    Certificate.inside)))
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                Certificate.inside))
            Certificate.inside)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (-9722078601752641 : ℤ) (45739683715481600 : ℕ) none)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.cross (-64458493329125689 : ℤ) (182958734861926400 : ℕ) none)
                      (Certificate.cross (-781069560174911 : ℤ) (1759218604441600 : ℕ) none))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.cross (-1277567086578814009 : ℤ) (6305039478318694400 : ℕ) none)
                            (Certificate.cross (-961833145022846423 : ℤ) (2476979795053772800 : ℕ) none)))
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            (Certificate.cross (-280968311000606278277 : ℤ) (807045053224792883200 : ℕ) none)
                            (Certificate.cross (-16102193928976348643 : ℤ) (39631676720860364800 : ℕ) none))
                          (Certificate.splitX (264 : ℤ)
                            (Certificate.cross (-14500984247628627259 : ℤ) (33326637242541670400 : ℕ) none)
                            Certificate.outside))))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (-120675492230235503 : ℤ) (365917469723852800 : ℕ) none)
                      (Certificate.cross (-51080686517745391 : ℤ) (98516241848729600 : ℕ) none)))
                  (Certificate.cross (-5875661006728501 : ℤ) (10555311626649600 : ℕ) none))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-555486124467563 : ℤ) (6377167441100800 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.cross (-370279634500169689 : ℤ) (675539944105574400 : ℕ) none)
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (720 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)))))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-5076894474343501 : ℤ) (25948474415513600 : ℕ) none)
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (864 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (816 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (792 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (840 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              (Certificate.splitX (852 : ℤ)
                                (Certificate.splitY (-228 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-228 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside)))))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (912 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (888 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-264 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          (Certificate.splitX (888 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              (Certificate.splitX (876 : ℤ)
                                (Certificate.splitY (-228 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-228 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (936 : ℤ)
                            (Certificate.splitY (-264 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-264 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside))))
                  (Certificate.splitX (864 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1008 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (984 : ℤ)
                            (Certificate.splitY (-264 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (1104 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside))
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (1200 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (1296 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (1392 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.splitX (1512 : ℤ)
                            (Certificate.splitY (-360 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-360 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-372 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside))
                          Certificate.outside))
                      Certificate.outside))
                  Certificate.outside)))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-441927096204827689 : ℤ) (816277432460902400 : ℕ) none)
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
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (264 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (264 : ℤ)
                              Certificate.outside
                              Certificate.outside))))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside)))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside))
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)
                Certificate.outside)
              Certificate.outside))
          Certificate.outside)
        Certificate.outside)],
    ![
      (Certificate.splitX (-768 : ℤ)
        Certificate.inside
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
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      Certificate.inside)))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    Certificate.inside)))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          Certificate.inside))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      Certificate.inside)
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
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (252 : ℤ)
                                  Certificate.inside
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)))
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1464 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside))))
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1392 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1296 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1200 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside))))
              Certificate.inside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1056 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      Certificate.inside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside))
              Certificate.inside))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-18187147891424157 : ℤ) (77405618595430400 : ℕ) none))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-264 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-4304276828218865259 : ℤ) (12610078956637388800 : ℕ) none))))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-28902514327282503 : ℤ) (98516241848729600 : ℕ) none)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              (Certificate.cross (-323126389189500057819 : ℤ) (922337203685477580800 : ℕ) none)
                              (Certificate.cross (-81956098630567000947 : ℤ) (208967022709991014400 : ℕ) none))
                            (Certificate.cross (-11656211732017023 : ℤ) (28147497671065600 : ℕ) none))))
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-428517541999290381 : ℤ) (1041457413829427200 : ℕ) none)
                        Certificate.outside))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-7441089912497523 : ℤ) (28147497671065600 : ℕ) none))
                    (Certificate.cross (-9027403051956129 : ℤ) (22869841857740800 : ℕ) none))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.cross (-5422734856199167173 : ℤ) (11709359031163289600 : ℕ) none)
                      Certificate.outside)
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.cross (-62580653786272883 : ℤ) (116108427893145600 : ℕ) none)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      Certificate.outside))))))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.cross (-3659542706329563 : ℤ) (19351404648857600 : ℕ) none)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (864 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (816 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (840 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)))))
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (912 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (888 : ℤ)
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              Certificate.outside))
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside)))))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1056 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside))))
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (864 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (816 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.splitY (792 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.splitY (840 : ℤ)
                              (Certificate.splitX (-180 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              Certificate.outside)
                            Certificate.outside))
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (1248 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    Certificate.outside)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (1488 : ℤ)
                          (Certificate.splitX (-360 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          (Certificate.splitX (-360 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-348 : ℤ)
                                Certificate.outside
                                Certificate.outside))))
                        Certificate.outside))
                    Certificate.outside))
                Certificate.outside))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (252 : ℤ)
                                Certificate.inside
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.inside
                            Certificate.inside)))
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-1248 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside)))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-960 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                (Certificate.splitY (-960 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    Certificate.inside)
                  Certificate.inside)))
            Certificate.inside)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (-5964654822518157 : ℤ) (77405618595430400 : ℕ) none)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.cross (-7441089912497523 : ℤ) (28147497671065600 : ℕ) none)
                      (Certificate.cross (-9027403051956129 : ℤ) (22869841857740800 : ℕ) none))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-28902514327282503 : ℤ) (98516241848729600 : ℕ) none))
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-4304276828218865259 : ℤ) (12610078956637388800 : ℕ) none))
                          (Certificate.splitX (264 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              (Certificate.cross (-323126389189500057819 : ℤ) (922337203685477580800 : ℕ) none)
                              (Certificate.cross (-2470868887639141221 : ℤ) (6530219459687219200 : ℕ) none))
                            (Certificate.cross (-11656211732017023 : ℤ) (28147497671065600 : ℕ) none)))))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (-18187147891424157 : ℤ) (77405618595430400 : ℕ) none)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.cross (-473401152454033131 : ℤ) (1041457413829427200 : ℕ) none)
                        Certificate.outside)))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.cross (-144726255711415407 : ℤ) (288511851128422400 : ℕ) none)
                    Certificate.outside))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.cross (-7269999893607659 : ℤ) (14073748835532800 : ℕ) none)
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (720 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)))))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-986636507564313 : ℤ) (12754334882201600 : ℕ) none)
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (864 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (816 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (840 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (852 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)))))))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (912 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (888 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (876 : ℤ)
                                Certificate.outside
                                Certificate.outside))
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (936 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside))))))
                  (Certificate.splitX (864 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (816 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (792 : ℤ)
                            (Certificate.splitY (-168 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-168 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (840 : ℤ)
                            (Certificate.splitY (-168 : ℤ)
                              (Certificate.splitX (828 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              Certificate.outside)
                            Certificate.outside)
                          Certificate.outside))
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1008 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1104 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)))
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (1200 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (1296 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (1392 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.splitX (1464 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-360 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.splitX (1512 : ℤ)
                            (Certificate.splitY (-360 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-360 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-348 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))))
                          Certificate.outside))
                      Certificate.outside))
                  Certificate.outside)))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-417903479139744939 : ℤ) (788129934789836800 : ℕ) none)
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
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (312 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside))
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)
                Certificate.outside)
              Certificate.outside))
          Certificate.outside)
        Certificate.outside)],
    ![
      (Certificate.splitX (-768 : ℤ)
        Certificate.inside
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
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      Certificate.inside)))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    Certificate.inside)))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-264 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          Certificate.inside))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (276 : ℤ)
                                  Certificate.inside
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (282 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside))
                                (Certificate.splitY (276 : ℤ)
                                  Certificate.inside
                                  Certificate.inside)))
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)))
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1464 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside))))
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1392 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1296 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1200 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside))))
              Certificate.inside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1056 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1104 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1008 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-816 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          Certificate.inside))))
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)))
              Certificate.inside))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (-696 : ℤ)
                            (Certificate.splitY (120 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (120 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside)))
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-624 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (-648 : ℤ)
                            (Certificate.splitY (120 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (120 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (-600 : ℤ)
                            (Certificate.splitY (120 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside))))
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (-237707194709251 : ℤ) (1979120929996800 : ℕ) none)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-1157927101997239759 : ℤ) (5404319552844595200 : ℕ) none)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-61573877959596649 : ℤ) (337769972052787200 : ℕ) none)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              (Certificate.cross (-767672344002382595483 : ℤ) (2767011611056432742400 : ℕ) none)
                              (Certificate.cross (-52899917507184500447 : ℤ) (151320947479648665600 : ℕ) none))
                            (Certificate.cross (-96454427776973003 : ℤ) (253327479039590400 : ℕ) none))))
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-41531281700077157 : ℤ) (116108427893145600 : ℕ) none)
                        Certificate.outside))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-113545598705420881 : ℤ) (506654958079180800 : ℕ) none))
                    (Certificate.cross (-7975094174893129 : ℤ) (21110623253299200 : ℕ) none))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-85607433572080728947 : ℤ) (259407338536540569600 : ℕ) none)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.cross (-14290699222987877 : ℤ) (28147497671065600 : ℕ) none)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)))))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.cross (-1704797537112563 : ℤ) (19131502323302400 : ℕ) none)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (864 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (912 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (936 : ℤ)
                              Certificate.outside
                              Certificate.outside))))))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1056 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1008 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (1104 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))))
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (864 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (816 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-168 : ℤ)
                            Certificate.outside
                            Certificate.outside))
                        Certificate.outside)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (912 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    Certificate.outside)
                  Certificate.outside))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (1248 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (1248 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1392 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-312 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          (Certificate.splitX (-312 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          (Certificate.splitX (-312 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-324 : ℤ)
                                Certificate.outside
                                Certificate.outside))
                            Certificate.outside))))
                    Certificate.outside))
                Certificate.outside))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (276 : ℤ)
                                Certificate.inside
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (282 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside))
                              Certificate.inside))
                          (Certificate.splitX (264 : ℤ)
                            Certificate.inside
                            Certificate.inside)))
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-1248 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside)))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-960 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-864 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        Certificate.inside))))
                (Certificate.splitY (-960 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-1056 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    Certificate.inside))))
            Certificate.inside)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (-720 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (120 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        Certificate.inside)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (-624 : ℤ)
                          (Certificate.splitX (120 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          (Certificate.splitX (120 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        Certificate.inside)))
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (-626302958185157 : ℤ) (63331869759897600 : ℕ) none)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.cross (-113545598705420881 : ℤ) (506654958079180800 : ℕ) none)
                      (Certificate.cross (-7975094174893129 : ℤ) (21110623253299200 : ℕ) none))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.cross (-61573877959596649 : ℤ) (337769972052787200 : ℕ) none)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-1157927101997239759 : ℤ) (5404319552844595200 : ℕ) none)
                          (Certificate.splitX (264 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              (Certificate.cross (-767672344002382595483 : ℤ) (2767011611056432742400 : ℕ) none)
                              (Certificate.cross (-3246495489079103567 : ℤ) (9457559217478041600 : ℕ) none))
                            (Certificate.cross (-96454427776973003 : ℤ) (253327479039590400 : ℕ) none)))))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (-237707194709251 : ℤ) (1979120929996800 : ℕ) none)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-85600794496054607447 : ℤ) (259407338536540569600 : ℕ) none)
                          Certificate.outside)
                        Certificate.outside)))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.cross (-22140951612128245759 : ℤ) (59447515081290547200 : ℕ) none)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.cross (-4216321749617063 : ℤ) (7036874417766400 : ℕ) none)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (864 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (912 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (888 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (936 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside))))))
                  (Certificate.splitX (864 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (816 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (840 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-168 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (912 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1008 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (984 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1032 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside))))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1104 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside))))
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1200 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (1296 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (1392 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1416 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-312 : ℤ)
                              Certificate.outside
                              Certificate.outside))))
                      Certificate.outside)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1464 : ℤ)
                            (Certificate.splitY (-312 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-312 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            (Certificate.splitY (-312 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-312 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                (Certificate.splitY (-324 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-324 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside))))
                      Certificate.outside))
                  Certificate.outside)))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.cross (-70164357033879383 : ℤ) (112589990684262400 : ℕ) none)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (312 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside))
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)
                Certificate.outside)
              Certificate.outside))
          Certificate.outside)
        Certificate.outside)],
    ![
      (Certificate.splitX (-768 : ℤ)
        Certificate.inside
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
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      Certificate.inside)))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    Certificate.inside)))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-264 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          Certificate.inside))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (312 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (300 : ℤ)
                                  Certificate.inside
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (306 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside))
                                (Certificate.splitY (300 : ℤ)
                                  Certificate.inside
                                  Certificate.inside))
                              Certificate.inside)
                            (Certificate.splitY (312 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-1464 : ℤ)
                            (Certificate.splitY (312 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside)))
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1392 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside))))
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1296 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1200 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside))))
              Certificate.inside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1056 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1104 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1008 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-864 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-816 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-792 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (168 : ℤ)
                              Certificate.inside
                              Certificate.inside))))))
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-912 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-816 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside))))
              Certificate.inside))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-744 : ℤ)
                            (Certificate.splitY (168 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (168 : ℤ)
                              Certificate.inside
                              Certificate.inside)))
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-696 : ℤ)
                            (Certificate.splitY (168 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (168 : ℤ)
                              Certificate.inside
                              Certificate.inside)))))
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-624 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          Certificate.inside))))
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (-17889822039152503 : ℤ) (197032483697459200 : ℕ) none)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-57735643290596182019 : ℤ) (187349744498612633600 : ℕ) none))
                            (Certificate.cross (-134811067315200131 : ℤ) (394064967394918400 : ℕ) none))))
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.cross (-17520375465505708967 : ℤ) (57646075230342348800 : ℕ) none)
                          (Certificate.cross (-1088800153238394149 : ℤ) (3265109729843609600 : ℕ) none))
                        (Certificate.cross (-2904675125711581 : ℤ) (7036874417766400 : ℕ) none)))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.cross (-56836384474742381 : ℤ) (394064967394918400 : ℕ) none)
                    (Certificate.cross (-6753573973444379 : ℤ) (19351404648857600 : ℕ) none))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-109590896228997534269 : ℤ) (403522526612396441600 : ℕ) none)
                          (Certificate.cross (-39431702585045750893 : ℤ) (104483511354995507200 : ℕ) none))
                        (Certificate.cross (-8065854456411976721 : ℤ) (19815838360430182400 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.cross (-52606305700725383 : ℤ) (109071553475379200 : ℕ) none)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)))))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (864 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (912 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside)))))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1056 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1008 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (984 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.splitY (1032 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)))
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1104 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside)))))
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (864 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    Certificate.outside)
                  Certificate.outside))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1248 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    Certificate.outside))
                Certificate.outside))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (300 : ℤ)
                                Certificate.inside
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (306 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside))
                              Certificate.inside)
                            Certificate.inside)
                          (Certificate.splitX (312 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        Certificate.inside)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        Certificate.inside)))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-1248 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside)))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-960 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-864 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-816 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (168 : ℤ)
                            Certificate.inside
                            Certificate.inside))))))
                (Certificate.splitY (-960 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-1056 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-864 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside))))
            Certificate.inside)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-720 : ℤ)
                          (Certificate.splitX (168 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          (Certificate.splitX (168 : ℤ)
                            Certificate.inside
                            Certificate.inside)))
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (-624 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside)))
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.cross (-56836384474742381 : ℤ) (394064967394918400 : ℕ) none)
                      (Certificate.cross (-6753573973444379 : ℤ) (19351404648857600 : ℕ) none))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (264 : ℤ)
                            (Certificate.cross (-1635289448790894817 : ℤ) (5854679515581644800 : ℕ) none)
                            (Certificate.splitY (-216 : ℤ)
                              (Certificate.cross (-57735643290596182019 : ℤ) (187349744498612633600 : ℕ) none)
                              (Certificate.cross (-134811067315200131 : ℤ) (394064967394918400 : ℕ) none))))))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (-17889822039152503 : ℤ) (197032483697459200 : ℕ) none)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-17520375465505708967 : ℤ) (57646075230342348800 : ℕ) none)
                          (Certificate.cross (-78973945059500939 : ℤ) (204069358115225600 : ℕ) none))
                        (Certificate.cross (-2904675125711581 : ℤ) (7036874417766400 : ℕ) none))))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.cross (-34703574672779762893 : ℤ) (104483511354995507200 : ℕ) none)
                        (Certificate.cross (-8065854456411976721 : ℤ) (19815838360430182400 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.cross (-62118199352903633 : ℤ) (109071553475379200 : ℕ) none)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (672 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (864 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (912 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (936 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside))))))
                  (Certificate.splitX (864 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (816 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (912 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1008 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (984 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1032 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1104 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1080 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside))))
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1200 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1296 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)))
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.cross (-134724488837641891 : ℤ) (218143106950758400 : ℕ) none)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside)))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (312 : ℤ)
                            Certificate.outside
                            Certificate.outside))
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.splitY (312 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside)))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    Certificate.outside)
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
        Certificate.inside
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          Certificate.inside))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      Certificate.inside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside))
                    Certificate.inside)
                  Certificate.inside)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (312 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (324 : ℤ)
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (318 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside)
                                  Certificate.inside)
                                (Certificate.splitY (324 : ℤ)
                                  Certificate.inside
                                  Certificate.inside)))
                            (Certificate.splitY (312 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1500 : ℤ)
                                (Certificate.splitY (324 : ℤ)
                                  Certificate.inside
                                  Certificate.inside)
                                Certificate.inside)))
                          Certificate.inside)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-1464 : ℤ)
                            (Certificate.splitY (312 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (312 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside)))
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1392 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-1416 : ℤ)
                            (Certificate.splitY (312 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (312 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-1368 : ℤ)
                            (Certificate.splitY (312 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (312 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside)))))
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1296 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-1320 : ℤ)
                            (Certificate.splitY (312 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1200 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside))))
              Certificate.inside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1056 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1104 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1008 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-912 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-888 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-816 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-840 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-792 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside))
                      Certificate.inside))))
              Certificate.inside))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-720 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          Certificate.inside)))
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-624 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          Certificate.inside))))
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-744 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    Certificate.inside))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.cross (-55336000350806069701 : ℤ) (288230376151711744000 : ℕ) none)
                            (Certificate.splitY (264 : ℤ)
                              (Certificate.cross (-6444068343127417697 : ℤ) (36028797018963968000 : ℕ) none)
                              (Certificate.cross (-653719394771446673 : ℤ) (2251799813685248000 : ℕ) none)))))
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-1463494653367747673 : ℤ) (5629499534213120000 : ℕ) none)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.cross (-14924802005931104509 : ℤ) (45035996273704960000 : ℕ) none)
                          Certificate.outside)))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.cross (-245521443473943923 : ℤ) (2251799813685248000 : ℕ) none)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                      (Certificate.cross (-2994400912522127 : ℤ) (8796093022208000 : ℕ) none)))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-270586667809771627201 : ℤ) (1152921504606846976000 : ℕ) none)
                          (Certificate.cross (-121516850757155786447 : ℤ) (360287970189639680000 : ℕ) none))
                        (Certificate.cross (-26883372677739971509 : ℤ) (72057594037927936000 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.cross (-14936767843845211 : ℤ) (35184372088832000 : ℕ) none)
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1056 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1008 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1104 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1080 : ℤ)
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              Certificate.outside))
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.splitY (1128 : ℤ)
                              (Certificate.splitX (-228 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              (Certificate.splitX (-228 : ℤ)
                                Certificate.outside
                                Certificate.outside))
                            Certificate.outside))))))
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (864 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1248 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1200 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside))))
                Certificate.outside))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (312 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (324 : ℤ)
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (318 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside)
                              (Certificate.splitX (324 : ℤ)
                                Certificate.inside
                                Certificate.inside)))
                          (Certificate.splitX (312 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        Certificate.inside)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-1392 : ℤ)
                          (Certificate.splitX (312 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          (Certificate.splitX (312 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        Certificate.inside)))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-1248 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    (Certificate.splitY (-1248 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-1296 : ℤ)
                          (Certificate.splitX (312 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside))))
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-960 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-1056 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1008 : ℤ)
                          Certificate.inside
                          Certificate.inside)))
                    Certificate.inside)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-864 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-912 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (216 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        Certificate.inside)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-816 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          (Certificate.splitX (216 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        Certificate.inside))
                    Certificate.inside))))
            Certificate.inside)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        Certificate.inside)))
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-720 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.cross (-245521443473943923 : ℤ) (2251799813685248000 : ℕ) none)
                      (Certificate.cross (-2994400912522127 : ℤ) (8796093022208000 : ℕ) none))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (264 : ℤ)
                            (Certificate.cross (-6444068343127417697 : ℤ) (36028797018963968000 : ℕ) none)
                            (Certificate.splitY (-216 : ℤ)
                              (Certificate.cross (-55336000350806069701 : ℤ) (288230376151711744000 : ℕ) none)
                              (Certificate.cross (-653719394771446673 : ℤ) (2251799813685248000 : ℕ) none))))))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-244868704617980627701 : ℤ) (1152921504606846976000 : ℕ) none)
                          (Certificate.cross (-14924802005931104509 : ℤ) (45035996273704960000 : ℕ) none))
                        (Certificate.cross (-49908966860591657 : ℤ) (140737488355328000 : ℕ) none))))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-270586667809771627201 : ℤ) (1152921504606846976000 : ℕ) none)
                          (Certificate.cross (-110627537763801333947 : ℤ) (360287970189639680000 : ℕ) none))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-121516850757155786447 : ℤ) (360287970189639680000 : ℕ) none)
                          Certificate.outside))
                      Certificate.outside)
                    Certificate.outside))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.cross (-9162957391097543 : ℤ) (17592186044416000 : ℕ) none)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (864 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1008 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1032 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1104 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1080 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1068 : ℤ)
                                Certificate.outside
                                Certificate.outside))
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1128 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              (Certificate.splitX (1116 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-228 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              (Certificate.splitX (1140 : ℤ)
                                (Certificate.splitY (-228 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                Certificate.outside)
                              Certificate.outside))))))
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1200 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1176 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1224 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside))))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1296 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside))))
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1392 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)))
                  Certificate.outside)))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-1466649189333418381 : ℤ) (2814749767106560000 : ℕ) none)
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.splitY (312 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside)))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
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

end BerryEsseen.N2NeededIntegerPointwise09

#print axioms BerryEsseen.N2NeededIntegerPointwise09.powers_entries
#print axioms BerryEsseen.N2NeededIntegerPointwise09.powers_eq
#print axioms BerryEsseen.N2NeededIntegerPointwise09.checks
#print axioms BerryEsseen.N2NeededIntegerPointwise09.pointwise
