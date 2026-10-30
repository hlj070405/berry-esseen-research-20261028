module

public import BerryEsseen.N2NeededIntegerData
public import BerryEsseen.N2IntegerPointwiseReplay

@[expose] public section

/-! 2026-10-29: integer power numerators and the unchanged original
rows035..039 closed trees. The entries equality is the semantic cache bridge.
No Bernstein coefficient or host closed flag is a premise. -/

namespace BerryEsseen.N2NeededIntegerPointwise06

open N2NeededData N2NeededIntegerData N2IntegerBernstein
  N2IntegerRectangleCertificate N2MajorantPolynomials

def rowIndex (j : Fin 5) : Fin 65 :=
  ⟨6 * 5 + j.val,
    lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (6 * 5)) (by decide)⟩

def signX : Fin 4 → ℚ := N2IntegerPointwiseReplay.signX
def signY : Fin 4 → ℚ := N2IntegerPointwiseReplay.signY

def powers : Fin 5 → Fin 4 → IntPower :=
  ![
    ![
      ![![(367204368516539 : ℤ), (-303430536232125 : ℤ), (-46263422864125 : ℤ), (-1976716690875 : ℤ)],
        ![(-303430536232125 : ℤ), (675982456875 : ℤ), (207679331947500 : ℤ), (49267029094750 : ℤ)],
        ![(-46263422864125 : ℤ), (207679331947500 : ℤ), (-91204089374125 : ℤ), (-54092679119000 : ℤ)],
        ![(-1976716690875 : ℤ), (49267029094750 : ℤ), (-54092679119000 : ℤ), (6453000421000 : ℤ)]],
      ![![(367204368516539 : ℤ), (-303430536232125 : ℤ), (-46263422864125 : ℤ), (61150507559125 : ℤ)],
        ![(-303430536232125 : ℤ), (675982456875 : ℤ), (207679331947500 : ℤ), (-51470378117000 : ℤ)],
        ![(-46263422864125 : ℤ), (207679331947500 : ℤ), (-91204089374125 : ℤ), (-11729887416250 : ℤ)],
        ![(-1976716690875 : ℤ), (49267029094750 : ℤ), (-54092679119000 : ℤ), (-9777388254500 : ℤ)]],
      ![![(367204368516539 : ℤ), (-303430536232125 : ℤ), (-46263422864125 : ℤ), (-1976716690875 : ℤ)],
        ![(-303430536232125 : ℤ), (675982456875 : ℤ), (207679331947500 : ℤ), (49267029094750 : ℤ)],
        ![(-46263422864125 : ℤ), (207679331947500 : ℤ), (-91204089374125 : ℤ), (-54092679119000 : ℤ)],
        ![(61150507559125 : ℤ), (-51470378117000 : ℤ), (-11729887416250 : ℤ), (-9777388254500 : ℤ)]],
      ![![(367204368516539 : ℤ), (-303430536232125 : ℤ), (-46263422864125 : ℤ), (61150507559125 : ℤ)],
        ![(-303430536232125 : ℤ), (675982456875 : ℤ), (207679331947500 : ℤ), (-51470378117000 : ℤ)],
        ![(-46263422864125 : ℤ), (207679331947500 : ℤ), (-91204089374125 : ℤ), (-11729887416250 : ℤ)],
        ![(61150507559125 : ℤ), (-51470378117000 : ℤ), (-11729887416250 : ℤ), (13101776088000 : ℤ)]]],
    ![
      ![![(375572153154914 : ℤ), (-310320083962875 : ℤ), (-51891367793875 : ℤ), (-4408576985875 : ℤ)],
        ![(-310320083962875 : ℤ), (-9628866912750 : ℤ), (217945555920125 : ℤ), (55114957513625 : ℤ)],
        ![(-51891367793875 : ℤ), (217945555920125 : ℤ), (-78751971632375 : ℤ), (-50155572583375 : ℤ)],
        ![(-4408576985875 : ℤ), (55114957513625 : ℤ), (-50155572583375 : ℤ), (7442635804250 : ℤ)]],
      ![![(375572153154914 : ℤ), (-310320083962875 : ℤ), (-51891367793875 : ℤ), (64431605483875 : ℤ)],
        ![(-310320083962875 : ℤ), (-9628866912750 : ℤ), (217945555920125 : ℤ), (-52765469512875 : ℤ)],
        ![(-51891367793875 : ℤ), (217945555920125 : ℤ), (-78751971632375 : ℤ), (-17535891154875 : ℤ)],
        ![(-4408576985875 : ℤ), (55114957513625 : ℤ), (-50155572583375 : ℤ), (-11276853424500 : ℤ)]],
      ![![(375572153154914 : ℤ), (-310320083962875 : ℤ), (-51891367793875 : ℤ), (-4408576985875 : ℤ)],
        ![(-310320083962875 : ℤ), (-9628866912750 : ℤ), (217945555920125 : ℤ), (55114957513625 : ℤ)],
        ![(-51891367793875 : ℤ), (217945555920125 : ℤ), (-78751971632375 : ℤ), (-50155572583375 : ℤ)],
        ![(64431605483875 : ℤ), (-52765469512875 : ℤ), (-17535891154875 : ℤ), (-11276853424500 : ℤ)]],
      ![![(375572153154914 : ℤ), (-310320083962875 : ℤ), (-51891367793875 : ℤ), (64431605483875 : ℤ)],
        ![(-310320083962875 : ℤ), (-9628866912750 : ℤ), (217945555920125 : ℤ), (-52765469512875 : ℤ)],
        ![(-51891367793875 : ℤ), (217945555920125 : ℤ), (-78751971632375 : ℤ), (-17535891154875 : ℤ)],
        ![(64431605483875 : ℤ), (-52765469512875 : ℤ), (-17535891154875 : ℤ), (15111071044750 : ℤ)]]],
    ![
      ![![(384036890712914 : ℤ), (-317189708447875 : ℤ), (-54509760489000 : ℤ), (-5029253757375 : ℤ)],
        ![(-317189708447875 : ℤ), (-21974555809625 : ℤ), (226069326013875 : ℤ), (60005500109375 : ℤ)],
        ![(-54509760489000 : ℤ), (226069326013875 : ℤ), (-74037878389875 : ℤ), (-49231095742250 : ℤ)],
        ![(-5029253757375 : ℤ), (60005500109375 : ℤ), (-49231095742250 : ℤ), (7808776317625 : ℤ)]],
      ![![(384036890712914 : ℤ), (-317189708447875 : ℤ), (-54509760489000 : ℤ), (67243587085125 : ℤ)],
        ![(-317189708447875 : ℤ), (-21974555809625 : ℤ), (226069326013875 : ℤ), (-51116829303625 : ℤ)],
        ![(-54509760489000 : ℤ), (226069326013875 : ℤ), (-74037878389875 : ℤ), (-21028921543750 : ℤ)],
        ![(-5029253757375 : ℤ), (60005500109375 : ℤ), (-49231095742250 : ℤ), (-11831618296625 : ℤ)]],
      ![![(384036890712914 : ℤ), (-317189708447875 : ℤ), (-54509760489000 : ℤ), (-5029253757375 : ℤ)],
        ![(-317189708447875 : ℤ), (-21974555809625 : ℤ), (226069326013875 : ℤ), (60005500109375 : ℤ)],
        ![(-54509760489000 : ℤ), (226069326013875 : ℤ), (-74037878389875 : ℤ), (-49231095742250 : ℤ)],
        ![(67243587085125 : ℤ), (-51116829303625 : ℤ), (-21028921543750 : ℤ), (-11831618296625 : ℤ)]],
      ![![(384036890712914 : ℤ), (-317189708447875 : ℤ), (-54509760489000 : ℤ), (67243587085125 : ℤ)],
        ![(-317189708447875 : ℤ), (-21974555809625 : ℤ), (226069326013875 : ℤ), (-51116829303625 : ℤ)],
        ![(-54509760489000 : ℤ), (226069326013875 : ℤ), (-74037878389875 : ℤ), (-21028921543750 : ℤ)],
        ![(67243587085125 : ℤ), (-51116829303625 : ℤ), (-21028921543750 : ℤ), (15854460275625 : ℤ)]]],
    ![
      ![![(394481142410664 : ℤ), (-322972379731625 : ℤ), (-61313826452875 : ℤ), (-6729097356625 : ℤ)],
        ![(-322972379731625 : ℤ), (-34330954359125 : ℤ), (232649869115250 : ℤ), (63555626742750 : ℤ)],
        ![(-61313826452875 : ℤ), (232649869115250 : ℤ), (-62625788106125 : ℤ), (-47244984898250 : ℤ)],
        ![(-6729097356625 : ℤ), (63555626742750 : ℤ), (-47244984898250 : ℤ), (8243932399750 : ℤ)]],
      ![![(394481142410664 : ℤ), (-322972379731625 : ℤ), (-61313826452875 : ℤ), (71079801886625 : ℤ)],
        ![(-322972379731625 : ℤ), (-34330954359125 : ℤ), (232649869115250 : ℤ), (-49126266384000 : ℤ)],
        ![(-61313826452875 : ℤ), (232649869115250 : ℤ), (-62625788106125 : ℤ), (-25599761715250 : ℤ)],
        ![(-6729097356625 : ℤ), (63555626742750 : ℤ), (-47244984898250 : ℤ), (-12490953441500 : ℤ)]],
      ![![(394481142410664 : ℤ), (-322972379731625 : ℤ), (-61313826452875 : ℤ), (-6729097356625 : ℤ)],
        ![(-322972379731625 : ℤ), (-34330954359125 : ℤ), (232649869115250 : ℤ), (63555626742750 : ℤ)],
        ![(-61313826452875 : ℤ), (232649869115250 : ℤ), (-62625788106125 : ℤ), (-47244984898250 : ℤ)],
        ![(71079801886625 : ℤ), (-49126266384000 : ℤ), (-25599761715250 : ℤ), (-12490953441500 : ℤ)]],
      ![![(394481142410664 : ℤ), (-322972379731625 : ℤ), (-61313826452875 : ℤ), (71079801886625 : ℤ)],
        ![(-322972379731625 : ℤ), (-34330954359125 : ℤ), (232649869115250 : ℤ), (-49126266384000 : ℤ)],
        ![(-61313826452875 : ℤ), (232649869115250 : ℤ), (-62625788106125 : ℤ), (-25599761715250 : ℤ)],
        ![(71079801886625 : ℤ), (-49126266384000 : ℤ), (-25599761715250 : ℤ), (16737974483250 : ℤ)]]],
    ![
      ![![(410379324596164 : ℤ), (-324720627430500 : ℤ), (-86708369389125 : ℤ), (-17130350584375 : ℤ)],
        ![(-324720627430500 : ℤ), (-64299573384250 : ℤ), (244178200365125 : ℤ), (77356356985375 : ℤ)],
        ![(-86708369389125 : ℤ), (244178200365125 : ℤ), (-13795639232750 : ℤ), (-33225511720875 : ℤ)],
        ![(-17130350584375 : ℤ), (77356356985375 : ℤ), (-33225511720875 : ℤ), (10677998631875 : ℤ)]],
      ![![(410379324596164 : ℤ), (-324720627430500 : ℤ), (-86708369389125 : ℤ), (82013900941375 : ℤ)],
        ![(-324720627430500 : ℤ), (-64299573384250 : ℤ), (244178200365125 : ℤ), (-45228494496625 : ℤ)],
        ![(-86708369389125 : ℤ), (244178200365125 : ℤ), (-13795639232750 : ℤ), (-42659993206875 : ℤ)],
        ![(-17130350584375 : ℤ), (77356356985375 : ℤ), (-33225511720875 : ℤ), (-16178975917125 : ℤ)]],
      ![![(410379324596164 : ℤ), (-324720627430500 : ℤ), (-86708369389125 : ℤ), (-17130350584375 : ℤ)],
        ![(-324720627430500 : ℤ), (-64299573384250 : ℤ), (244178200365125 : ℤ), (77356356985375 : ℤ)],
        ![(-86708369389125 : ℤ), (244178200365125 : ℤ), (-13795639232750 : ℤ), (-33225511720875 : ℤ)],
        ![(82013900941375 : ℤ), (-45228494496625 : ℤ), (-42659993206875 : ℤ), (-16178975917125 : ℤ)]],
      ![![(410379324596164 : ℤ), (-324720627430500 : ℤ), (-86708369389125 : ℤ), (82013900941375 : ℤ)],
        ![(-324720627430500 : ℤ), (-64299573384250 : ℤ), (244178200365125 : ℤ), (-45228494496625 : ℤ)],
        ![(-86708369389125 : ℤ), (244178200365125 : ℤ), (-13795639232750 : ℤ), (-42659993206875 : ℤ)],
        ![(82013900941375 : ℤ), (-45228494496625 : ℤ), (-42659993206875 : ℤ), (21679953202375 : ℤ)]]]]

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
                          (Certificate.splitX (-360 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-312 : ℤ)
                              Certificate.inside
                              Certificate.inside)))
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.splitX (-312 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          (Certificate.splitX (-312 : ℤ)
                            (Certificate.splitY (-312 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside)))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-107143134326946381 : ℤ) (309622474381721600 : ℕ) none))
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (-104718448155648413451 : ℤ) (403522526612396441600 : ℕ) none)
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.cross (-15132186845026072197 : ℤ) (50440315826549555200 : ℕ) none)
                              (Certificate.cross (-7272502910221761759 : ℤ) (19815838360430182400 : ℕ) none)))
                          (Certificate.cross (-38485272169183407 : ℤ) (91479367430963200 : ℕ) none))))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.cross (-15132186845026072197 : ℤ) (50440315826549555200 : ℕ) none)
                            (Certificate.cross (-7272502910221761759 : ℤ) (19815838360430182400 : ℕ) none)))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-107143134326946381 : ℤ) (309622474381721600 : ℕ) none)
                          (Certificate.cross (-38485272169183407 : ℤ) (91479367430963200 : ℕ) none)))
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.cross (-847764166862311780701 : ℤ) (2132904783522666905600 : ℕ) none)
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside))))))))),
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
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (60 : ℤ)
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (54 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside))
                        (Certificate.splitY (48 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)
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
                Certificate.inside
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.cross (-827459852401417 : ℤ) (1319413953331200 : ℕ) none)))
              (Certificate.cross (-3147306598343001 : ℤ) (6157265115545600 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-360 : ℤ)
                            (Certificate.cross (-7331370760282527393 : ℤ) (12610078956637388800 : ℕ) none)
                            (Certificate.splitY (168 : ℤ)
                              (Certificate.cross (-434481807505171789527 : ℤ) (807045053224792883200 : ℕ) none)
                              (Certificate.cross (-3068298225115508721 : ℤ) (4953959590107545600 : ℕ) none))))
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (-20624123899178399643 : ℤ) (39631676720860364800 : ℕ) none)
                          (Certificate.cross (-2241544630531265673 : ℤ) (3602879701896396800 : ℕ) none))))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-16334430278583773643 : ℤ) (39631676720860364800 : ℕ) none)
                        (Certificate.cross (-699727426196327637 : ℤ) (1463669878895411200 : ℕ) none))
                      (Certificate.cross (-899204604955816137 : ℤ) (1463669878895411200 : ℕ) none)))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (-69293338001388891 : ℤ) (98516241848729600 : ℕ) none)
                    Certificate.outside))
                (Certificate.cross (-11550363928925127 : ℤ) (16712576742195200 : ℕ) none))
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
                        Certificate.outside
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)))
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))
                  Certificate.outside))))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
            Certificate.outside))),
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
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (60 : ℤ)
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (54 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside))
                      Certificate.inside)
                    Certificate.inside)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              Certificate.inside)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.cross (-827459852401417 : ℤ) (1319413953331200 : ℕ) none))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.cross (-1744039623792166221 : ℤ) (4953959590107545600 : ℕ) none)
                        (Certificate.cross (-699727426196327637 : ℤ) (1463669878895411200 : ℕ) none)))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.cross (-20624123899178399643 : ℤ) (39631676720860364800 : ℕ) none)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-434481807505171789527 : ℤ) (807045053224792883200 : ℕ) none)
                            (Certificate.cross (-3068298225115508721 : ℤ) (4953959590107545600 : ℕ) none))
                          (Certificate.cross (-2241544630531265673 : ℤ) (3602879701896396800 : ℕ) none)))
                      (Certificate.cross (-899204604955816137 : ℤ) (1463669878895411200 : ℕ) none)))
                  (Certificate.cross (-230106700699864689 : ℤ) (394064967394918400 : ℕ) none))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.cross (-455300097006161253 : ℤ) (647392446434508800 : ℕ) none)
                    Certificate.outside)
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-3147306598343001 : ℤ) (6157265115545600 : ℕ) none)
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
                            (Certificate.splitY (-120 : ℤ)
                              Certificate.outside
                              Certificate.outside))))
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (504 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              Certificate.outside)
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              Certificate.outside)))),
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
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside))
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
                  Certificate.outside
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
                            (Certificate.splitY (648 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (648 : ℤ)
                              Certificate.outside
                              Certificate.outside))))
                      (Certificate.splitX (624 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (720 : ℤ)
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))))))
          (Certificate.splitX (384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside)
              (Certificate.splitX (576 : ℤ)
                Certificate.outside
                Certificate.outside))))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside))))
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
                          (Certificate.splitX (-360 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-312 : ℤ)
                              Certificate.inside
                              Certificate.inside)))
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.splitX (-312 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          (Certificate.splitX (-312 : ℤ)
                            (Certificate.splitY (-312 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside)))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-62516160950415381 : ℤ) (197032483697459200 : ℕ) none))
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (-120 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-72 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-18194490264191866911 : ℤ) (50440315826549555200 : ℕ) none)))
                          (Certificate.cross (-33217725077008407 : ℤ) (77405618595430400 : ℕ) none))))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-72 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-18194490264191866911 : ℤ) (50440315826549555200 : ℕ) none)))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-62516160950415381 : ℤ) (197032483697459200 : ℕ) none)
                          (Certificate.cross (-33217725077008407 : ℤ) (77405618595430400 : ℕ) none)))
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.cross (-9515353394984967386307 : ℤ) (25825441703193372262400 : ℕ) none)
                              (Certificate.cross (-2700369561345227998929 : ℤ) (6686944726719712460800 : ℕ) none))
                            (Certificate.cross (-541513715877335393163 : ℤ) (1268213655067531673600 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside))))))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-1440 : ℤ)
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
              Certificate.inside)
            (Certificate.splitY (384 : ℤ)
              Certificate.inside
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.cross (-8968052450756379 : ℤ) (14073748835532800 : ℕ) none)))
              (Certificate.cross (-1504914195384063 : ℤ) (2858730232217600 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-360 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-971734998950894673 : ℤ) (1576259869579673600 : ℕ) none)))
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (-12538516813170622893 : ℤ) (25220157913274777600 : ℕ) none)
                          (Certificate.cross (-601094209706553387 : ℤ) (957014920816230400 : ℕ) none))))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-9271717500178371393 : ℤ) (25220157913274777600 : ℕ) none)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.cross (-240996750060313899 : ℤ) (788129934789836800 : ℕ) none)
                          (Certificate.cross (-301068910570895631 : ℤ) (619244948763443200 : ℕ) none)))
                      (Certificate.cross (-48348949777349157 : ℤ) (77405618595430400 : ℕ) none)))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.cross (-2171624422320983141 : ℤ) (3152519739159347200 : ℕ) none)
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-12132309892870531971 : ℤ) (23418718062326579200 : ℕ) none)
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))
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
                        Certificate.outside
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)))
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))
                  Certificate.outside))))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
            Certificate.outside))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside)
              Certificate.inside)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.cross (-8968052450756379 : ℤ) (14073748835532800 : ℕ) none))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.cross (-240996750060313899 : ℤ) (788129934789836800 : ℕ) none)
                        (Certificate.cross (-301068910570895631 : ℤ) (619244948763443200 : ℕ) none)))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.cross (-12538516813170622893 : ℤ) (25220157913274777600 : ℕ) none)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.splitX (168 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-971734998950894673 : ℤ) (1576259869579673600 : ℕ) none))
                          (Certificate.cross (-601094209706553387 : ℤ) (957014920816230400 : ℕ) none)))
                      (Certificate.cross (-48348949777349157 : ℤ) (77405618595430400 : ℕ) none)))
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (-456574849110387003 : ℤ) (872572427803033600 : ℕ) none)
                    Certificate.outside))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (-2171624422320983141 : ℤ) (3152519739159347200 : ℕ) none)
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-1504914195384063 : ℤ) (2858730232217600 : ℕ) none)
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
                            (Certificate.splitY (-120 : ℤ)
                              Certificate.outside
                              Certificate.outside))))
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              Certificate.outside)
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              Certificate.outside)))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside))
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
                    Certificate.outside)))
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
                Certificate.outside
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (624 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (648 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (648 : ℤ)
                              Certificate.outside
                              Certificate.outside))))
                      (Certificate.splitX (624 : ℤ)
                        (Certificate.splitY (720 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (720 : ℤ)
                          (Certificate.splitX (648 : ℤ)
                            (Certificate.splitY (696 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)
                          Certificate.outside)))
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (720 : ℤ)
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (696 : ℤ)
                            (Certificate.splitY (648 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside))
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside))))))
          (Certificate.splitX (384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (864 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1056 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        Certificate.outside))))
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (864 : ℤ)
                      (Certificate.splitX (624 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1248 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside))
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1392 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (456 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          (Certificate.splitX (456 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          (Certificate.splitX (456 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              (Certificate.splitX (468 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              (Certificate.splitX (468 : ℤ)
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (462 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))
                                Certificate.outside))))))
                    Certificate.outside))
                Certificate.outside))))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (864 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (816 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (912 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside))))
                  (Certificate.splitX (864 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (816 : ℤ)
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1008 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1104 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside))))
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1200 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (1392 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1416 : ℤ)
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              Certificate.outside))))
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1464 : ℤ)
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1500 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (468 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)))
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                (Certificate.splitY (468 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (468 : ℤ)
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (462 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))
                                  Certificate.outside))))))
                      Certificate.outside))
                  Certificate.outside))))
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
                          (Certificate.splitX (-360 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-312 : ℤ)
                              Certificate.inside
                              Certificate.inside)))
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.splitX (-312 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          (Certificate.splitX (-312 : ℤ)
                            (Certificate.splitY (-312 : ℤ)
                              (Certificate.splitX (-324 : ℤ)
                                Certificate.inside
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.cross (-4985981555288627 : ℤ) (28147497671065600 : ℕ) none)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-4581724181637428149 : ℤ) (14411518807585587200 : ℕ) none)
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (-311246765643839141 : ℤ) (788129934789836800 : ℕ) none)
                            (Certificate.cross (-3081841949712323 : ℤ) (7036874417766400 : ℕ) none)))))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-4581724181637428149 : ℤ) (14411518807585587200 : ℕ) none))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-4985981555288627 : ℤ) (28147497671065600 : ℕ) none)
                          (Certificate.splitX (-24 : ℤ)
                            (Certificate.cross (-163057266623467271317 : ℤ) (403522526612396441600 : ℕ) none)
                            (Certificate.cross (-3081841949712323 : ℤ) (7036874417766400 : ℕ) none))))
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.cross (-2516796955077838032413 : ℤ) (7378697629483820646400 : ℕ) none)
                              (Certificate.cross (-1326315903045774507911 : ℤ) (3228180212899171532800 : ℕ) none))
                            (Certificate.cross (-101058804497742752439 : ℤ) (230584300921369395200 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside))))))))),
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
                                  Certificate.inside
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
                Certificate.inside
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.cross (-16497036150075883 : ℤ) (24629060462182400 : ℕ) none)))
              (Certificate.cross (-4022082662047793 : ℤ) (7036874417766400 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-1039142529886502003 : ℤ) (1801439850948198400 : ℕ) none))
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (-4936890011972834149 : ℤ) (14411518807585587200 : ℕ) none)
                          (Certificate.cross (-3699075423357688721 : ℤ) (5854679515581644800 : ℕ) none))))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-1868867437765242649 : ℤ) (14411518807585587200 : ℕ) none)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.cross (-140952195488029253 : ℤ) (1801439850948198400 : ℕ) none)
                          (Certificate.cross (-219095321538355047 : ℤ) (450359962737049600 : ℕ) none)))
                      (Certificate.cross (-284140252948356797 : ℤ) (450359962737049600 : ℕ) none)))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-157398729527714733189 : ℤ) (230584300921369395200 : ℕ) none)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.cross (-82440055613613890399 : ℤ) (158526706883441459200 : ℕ) none)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))
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
                        Certificate.outside
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (504 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside))))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
            Certificate.outside))),
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
                                Certificate.inside
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
                Certificate.inside
                (Certificate.cross (-16497036150075883 : ℤ) (24629060462182400 : ℕ) none))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.cross (-140952195488029253 : ℤ) (1801439850948198400 : ℕ) none)
                        (Certificate.cross (-219095321538355047 : ℤ) (450359962737049600 : ℕ) none)))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.cross (-4936890011972834149 : ℤ) (14411518807585587200 : ℕ) none)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.cross (-1039142529886502003 : ℤ) (1801439850948198400 : ℕ) none)
                          (Certificate.cross (-3699075423357688721 : ℤ) (5854679515581644800 : ℕ) none)))
                      (Certificate.cross (-284140252948356797 : ℤ) (450359962737049600 : ℕ) none)))
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.cross (-77839839693802803149 : ℤ) (158526706883441459200 : ℕ) none)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.cross (-157398729527714733189 : ℤ) (230584300921369395200 : ℕ) none)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-4022082662047793 : ℤ) (7036874417766400 : ℕ) none)
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
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (504 : ℤ)
                            (Certificate.splitY (-168 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              Certificate.outside)
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              Certificate.outside)))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside))
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
                    Certificate.outside)))
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
                Certificate.outside
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (624 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (720 : ℤ)
                          (Certificate.splitX (648 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (696 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          (Certificate.splitX (648 : ℤ)
                            Certificate.outside
                            Certificate.outside))))
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (720 : ℤ)
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (696 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (648 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (744 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (720 : ℤ)
                        (Certificate.splitY (720 : ℤ)
                          (Certificate.splitX (696 : ℤ)
                            (Certificate.splitY (696 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside)))))))
          (Certificate.splitX (384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (864 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1056 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        Certificate.outside))))
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (864 : ℤ)
                      (Certificate.splitX (624 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1248 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (456 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (468 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (474 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))))))))
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        Certificate.outside))))
                Certificate.outside))))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (864 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (912 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside))))
                  (Certificate.splitX (864 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (816 : ℤ)
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1008 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1104 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside))))
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1200 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1296 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside))))
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1392 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (468 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (474 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))))))))
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)))
                  Certificate.outside))))
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
                          (Certificate.splitX (-360 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-312 : ℤ)
                              Certificate.inside
                              Certificate.inside)))
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.splitX (-312 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          (Certificate.splitX (-312 : ℤ)
                            (Certificate.splitY (-312 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside)))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (-545933529173676673 : ℤ) (1463669878895411200 : ℕ) none)
                            (Certificate.cross (-21722844763902157 : ℤ) (49258120924364800 : ℕ) none)))))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-24 : ℤ)
                            (Certificate.cross (-146287610163237200413 : ℤ) (374699488997225267200 : ℕ) none)
                            (Certificate.cross (-21722844763902157 : ℤ) (49258120924364800 : ℕ) none))))
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.splitY (-72 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-1206795812508304696679 : ℤ) (2997595911977802137600 : ℕ) none))
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.cross (-1206795812508304696679 : ℤ) (2997595911977802137600 : ℕ) none)
                              (Certificate.cross (-50996260180011221059 : ℤ) (115292150460684697600 : ℕ) none)))
                          (Certificate.cross (-396609772117865381 : ℤ) (816277432460902400 : ℕ) none))
                        (Certificate.cross (-19409333934667 : ℤ) (37795712204800 : ℕ) none)))))))))),
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
                                  Certificate.inside
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (90 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside))
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
                Certificate.inside
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.cross (-289553106712771 : ℤ) (439804651110400 : ℕ) none)))
              (Certificate.cross (-174780717274211 : ℤ) (302365697638400 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-504360266957520637 : ℤ) (788129934789836800 : ℕ) none))))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (48 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-386952253751326387 : ℤ) (788129934789836800 : ℕ) none)))
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (-225123263646817427519 : ℤ) (403522526612396441600 : ℕ) none)
                          (Certificate.cross (-1372380165382096399 : ℤ) (2139209823000985600 : ℕ) none))
                        (Certificate.cross (-8310868557351074471 : ℤ) (13060438919374438400 : ℕ) none))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-276339999840227347019 : ℤ) (403522526612396441600 : ℕ) none)
                          (Certificate.cross (-2534596332417242117 : ℤ) (3602879701896396800 : ℕ) none))
                        (Certificate.cross (-8380664284314038939 : ℤ) (11709359031163289600 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.cross (-182895462319277191019 : ℤ) (403522526612396441600 : ℕ) none)
                          (Certificate.cross (-55600261841763926143 : ℤ) (104483511354995507200 : ℕ) none))
                        (Certificate.cross (-10807983105638542721 : ℤ) (19815838360430182400 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside))))
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (504 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside))))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)
              Certificate.outside)))),
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
                                Certificate.inside
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (90 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside))
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
                Certificate.inside
                (Certificate.cross (-289553106712771 : ℤ) (439804651110400 : ℕ) none))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (48 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-386952253751326387 : ℤ) (788129934789836800 : ℕ) none)))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-504360266957520637 : ℤ) (788129934789836800 : ℕ) none)))
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.cross (-7551036401768439221 : ℤ) (13060438919374438400 : ℕ) none)
                        (Certificate.cross (-144669983070762627 : ℤ) (225179981368524800 : ℕ) none))))
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.cross (-52396875965592923893 : ℤ) (104483511354995507200 : ℕ) none)
                        (Certificate.cross (-10807983105638542721 : ℤ) (19815838360430182400 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.cross (-276339999840227347019 : ℤ) (403522526612396441600 : ℕ) none)
                          (Certificate.cross (-40082848116679274137 : ℤ) (57646075230342348800 : ℕ) none))
                        (Certificate.cross (-1378700265516446387 : ℤ) (1914029841632460800 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-174780717274211 : ℤ) (302365697638400 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (504 : ℤ)
                            (Certificate.splitY (-168 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
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
                Certificate.outside))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              Certificate.outside)))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside))
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
                    Certificate.outside)))
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
                Certificate.outside
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside))))
          (Certificate.splitX (384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    Certificate.outside))
                (Certificate.splitY (960 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1248 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (528 : ℤ)
                        (Certificate.splitY (1488 : ℤ)
                          (Certificate.splitX (504 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          (Certificate.splitX (504 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (492 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (498 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))))
                            Certificate.outside))
                        Certificate.outside))))
                Certificate.outside))))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1296 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside))))
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1392 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          (Certificate.splitX (1464 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (504 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)
                        (Certificate.splitY (528 : ℤ)
                          (Certificate.splitX (1512 : ℤ)
                            (Certificate.splitY (504 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (504 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                (Certificate.splitY (492 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (492 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (498 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))))
                              Certificate.outside))
                          Certificate.outside))))
                  Certificate.outside))))
          Certificate.outside))],
    ![
      (Certificate.splitX (-768 : ℤ)
        Certificate.inside
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
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
                            (Certificate.splitY (-312 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside)))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (-145865290161836423 : ℤ) (562949953421312000 : ℕ) none)
                            (Certificate.splitY (-24 : ℤ)
                              (Certificate.cross (-85180161538956986701 : ℤ) (288230376151711744000 : ℕ) none)
                              (Certificate.cross (-14794885181002907 : ℤ) (35184372088832000 : ℕ) none))))))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-24 : ℤ)
                            (Certificate.cross (-85180161538956986701 : ℤ) (288230376151711744000 : ℕ) none)
                            (Certificate.cross (-14794885181002907 : ℤ) (35184372088832000 : ℕ) none))))
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.cross (-742340483729608518983 : ℤ) (2305843009213693952000 : ℕ) none)
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.cross (-742340483729608518983 : ℤ) (2305843009213693952000 : ℕ) none)
                              (Certificate.cross (-482625861808364279701 : ℤ) (1152921504606846976000 : ℕ) none)))
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.cross (-1786723566595996673 : ℤ) (3940649673949184000 : ℕ) none)
                            Certificate.outside))
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (-24 : ℤ)
                            (Certificate.cross (-7249262104341670777733 : ℤ) (16140901064495857664000 : ℕ) none)
                            Certificate.outside)
                          Certificate.outside)))))))))),
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
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (132 : ℤ)
                                  Certificate.inside
                                  Certificate.inside)
                                Certificate.inside))
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
              Certificate.inside
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.cross (-11427374127637133 : ℤ) (17592186044416000 : ℕ) none)))
              (Certificate.cross (-10887707918229379 : ℤ) (17592186044416000 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-312 : ℤ)
                            (Certificate.cross (-20059972780434597947 : ℤ) (36028797018963968000 : ℕ) none)
                            (Certificate.cross (-1409954799153906173 : ℤ) (2251799813685248000 : ℕ) none)))))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (48 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-1102926013702085423 : ℤ) (2251799813685248000 : ℕ) none)))
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (-639625929377094206701 : ℤ) (1152921504606846976000 : ℕ) none)
                          (Certificate.cross (-11432412588855096317 : ℤ) (18014398509481984000 : ℕ) none))
                        (Certificate.cross (-28544283575374104259 : ℤ) (45035996273704960000 : ℕ) none))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-761956933841111317201 : ℤ) (1152921504606846976000 : ℕ) none)
                          (Certificate.cross (-250284527743162136447 : ℤ) (360287970189639680000 : ℕ) none))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-392997608196458259769 : ℤ) (576460752303423488000 : ℕ) none)
                          Certificate.outside))
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.cross (-511545544918400641201 : ℤ) (1152921504606846976000 : ℕ) none)
                          (Certificate.cross (-192285552953147290697 : ℤ) (360287970189639680000 : ℕ) none))
                        (Certificate.cross (-39433249052400960259 : ℤ) (72057594037927936000 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside))))
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside))
                  Certificate.outside))))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)
              Certificate.outside)))),
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
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (132 : ℤ)
                                Certificate.inside
                                Certificate.inside)
                              Certificate.inside))
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside))
                  Certificate.inside)
                Certificate.inside)
              Certificate.inside)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.cross (-11427374127637133 : ℤ) (17592186044416000 : ℕ) none)))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (48 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-1102926013702085423 : ℤ) (2251799813685248000 : ℕ) none)))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-142565941070828425951 : ℤ) (288230376151711744000 : ℕ) none)
                            (Certificate.cross (-1409954799153906173 : ℤ) (2251799813685248000 : ℕ) none))))
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-639625929377094206701 : ℤ) (1152921504606846976000 : ℕ) none)
                          (Certificate.cross (-26170121652650408509 : ℤ) (45035996273704960000 : ℕ) none))
                        (Certificate.cross (-1432658743297244899 : ℤ) (2251799813685248000 : ℕ) none))))
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-511545544918400641201 : ℤ) (1152921504606846976000 : ℕ) none)
                          (Certificate.cross (-178766459506487493947 : ℤ) (360287970189639680000 : ℕ) none))
                        (Certificate.cross (-39433249052400960259 : ℤ) (72057594037927936000 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.cross (-761956933841111317201 : ℤ) (1152921504606846976000 : ℕ) none)
                          (Certificate.cross (-392997608196458259769 : ℤ) (576460752303423488000 : ℕ) none))
                        (Certificate.cross (-9596242168318679971 : ℤ) (13510798882111488000 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-10887707918229379 : ℤ) (17592186044416000 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (504 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)))
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
                Certificate.outside))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              Certificate.outside)))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (144 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)))
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
                    Certificate.outside)))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
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
          (Certificate.splitX (384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (576 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (528 : ℤ)
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (504 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (516 : ℤ)
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (510 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))
                                Certificate.outside))))
                        Certificate.outside))))
                Certificate.outside))))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (528 : ℤ)
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (504 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (516 : ℤ)
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (510 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))
                                  Certificate.outside))))
                          Certificate.outside))))
                  Certificate.outside))))
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

end BerryEsseen.N2NeededIntegerPointwise06

#print axioms BerryEsseen.N2NeededIntegerPointwise06.powers_entries
#print axioms BerryEsseen.N2NeededIntegerPointwise06.powers_eq
#print axioms BerryEsseen.N2NeededIntegerPointwise06.checks
#print axioms BerryEsseen.N2NeededIntegerPointwise06.pointwise
