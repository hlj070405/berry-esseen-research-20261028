module

public import BerryEsseen.N2NeededIntegerData
public import BerryEsseen.N2IntegerPointwiseReplay

@[expose] public section

/-! 2026-10-29: integer power numerators and the unchanged original
rows040..044 closed trees. The entries equality is the semantic cache bridge.
No Bernstein coefficient or host closed flag is a premise. -/

namespace BerryEsseen.N2NeededIntegerPointwise07

open N2NeededData N2NeededIntegerData N2IntegerBernstein
  N2IntegerRectangleCertificate N2MajorantPolynomials

def rowIndex (j : Fin 5) : Fin 65 :=
  ⟨7 * 5 + j.val,
    lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (7 * 5)) (by decide)⟩

def signX : Fin 4 → ℚ := N2IntegerPointwiseReplay.signX
def signY : Fin 4 → ℚ := N2IntegerPointwiseReplay.signY

def powers : Fin 5 → Fin 4 → IntPower :=
  ![
    ![
      ![![(421319263806789 : ℤ), (-329600756190000 : ℤ), (-93985820115625 : ℤ), (-20370448950250 : ℤ)],
        ![(-329600756190000 : ℤ), (-78109007819750 : ℤ), (249958383630750 : ℤ), (81600794239000 : ℤ)],
        ![(-93985820115625 : ℤ), (249958383630750 : ℤ), (-2564783922625 : ℤ), (-30348601285875 : ℤ)],
        ![(-20370448950250 : ℤ), (81600794239000 : ℤ), (-30348601285875 : ℤ), (10813426553625 : ℤ)]],
      ![![(421319263806789 : ℤ), (-329600756190000 : ℤ), (-93985820115625 : ℤ), (85977934582750 : ℤ)],
        ![(-329600756190000 : ℤ), (-78109007819750 : ℤ), (249958383630750 : ℤ), (-42560361829250 : ℤ)],
        ![(-93985820115625 : ℤ), (249958383630750 : ℤ), (-2564783922625 : ℤ), (-46400375537875 : ℤ)],
        ![(-20370448950250 : ℤ), (81600794239000 : ℤ), (-30348601285875 : ℤ), (-16384172149375 : ℤ)]],
      ![![(421319263806789 : ℤ), (-329600756190000 : ℤ), (-93985820115625 : ℤ), (-20370448950250 : ℤ)],
        ![(-329600756190000 : ℤ), (-78109007819750 : ℤ), (249958383630750 : ℤ), (81600794239000 : ℤ)],
        ![(-93985820115625 : ℤ), (249958383630750 : ℤ), (-2564783922625 : ℤ), (-30348601285875 : ℤ)],
        ![(85977934582750 : ℤ), (-42560361829250 : ℤ), (-46400375537875 : ℤ), (-16384172149375 : ℤ)]],
      ![![(421319263806789 : ℤ), (-329600756190000 : ℤ), (-93985820115625 : ℤ), (85977934582750 : ℤ)],
        ![(-329600756190000 : ℤ), (-78109007819750 : ℤ), (249958383630750 : ℤ), (-42560361829250 : ℤ)],
        ![(-93985820115625 : ℤ), (249958383630750 : ℤ), (-2564783922625 : ℤ), (-46400375537875 : ℤ)],
        ![(85977934582750 : ℤ), (-42560361829250 : ℤ), (-46400375537875 : ℤ), (21954917745125 : ℤ)]]],
    ![
      ![![(434123491949289 : ℤ), (-331358673423750 : ℤ), (-102357162836750 : ℤ), (-25105970611375 : ℤ)],
        ![(-331358673423750 : ℤ), (-95445452493875 : ℤ), (250468175893875 : ℤ), (85317578663750 : ℤ)],
        ![(-102357162836750 : ℤ), (250468175893875 : ℤ), (7308353108125 : ℤ), (-26452657390250 : ℤ)],
        ![(-25105970611375 : ℤ), (85317578663750 : ℤ), (-26452657390250 : ℤ), (11107441993750 : ℤ)]],
      ![![(434123491949289 : ℤ), (-331358673423750 : ℤ), (-102357162836750 : ℤ), (88742587467625 : ℤ)],
        ![(-331358673423750 : ℤ), (-95445452493875 : ℤ), (250468175893875 : ℤ), (-37290531564000 : ℤ)],
        ![(-102357162836750 : ℤ), (250468175893875 : ℤ), (7308353108125 : ℤ), (-45173001364750 : ℤ)],
        ![(-25105970611375 : ℤ), (85317578663750 : ℤ), (-26452657390250 : ℤ), (-15101962943250 : ℤ)]],
      ![![(434123491949289 : ℤ), (-331358673423750 : ℤ), (-102357162836750 : ℤ), (-25105970611375 : ℤ)],
        ![(-331358673423750 : ℤ), (-95445452493875 : ℤ), (250468175893875 : ℤ), (85317578663750 : ℤ)],
        ![(-102357162836750 : ℤ), (250468175893875 : ℤ), (7308353108125 : ℤ), (-26452657390250 : ℤ)],
        ![(88742587467625 : ℤ), (-37290531564000 : ℤ), (-45173001364750 : ℤ), (-15101962943250 : ℤ)]],
      ![![(434123491949289 : ℤ), (-331358673423750 : ℤ), (-102357162836750 : ℤ), (88742587467625 : ℤ)],
        ![(-331358673423750 : ℤ), (-95445452493875 : ℤ), (250468175893875 : ℤ), (-37290531564000 : ℤ)],
        ![(-102357162836750 : ℤ), (250468175893875 : ℤ), (7308353108125 : ℤ), (-45173001364750 : ℤ)],
        ![(88742587467625 : ℤ), (-37290531564000 : ℤ), (-45173001364750 : ℤ), (19096483892750 : ℤ)]]],
    ![
      ![![(449036680073414 : ℤ), (-328039072733375 : ℤ), (-109423919409000 : ℤ), (-28917389293750 : ℤ)],
        ![(-328039072733375 : ℤ), (-118044152985500 : ℤ), (245038868941000 : ℤ), (88900927694000 : ℤ)],
        ![(-109423919409000 : ℤ), (245038868941000 : ℤ), (2781173629250 : ℤ), (-30609857541250 : ℤ)],
        ![(-28917389293750 : ℤ), (88900927694000 : ℤ), (-30609857541250 : ℤ), (6806372087250 : ℤ)]],
      ![![(449036680073414 : ℤ), (-328039072733375 : ℤ), (-109423919409000 : ℤ), (87908446464750 : ℤ)],
        ![(-328039072733375 : ℤ), (-118044152985500 : ℤ), (245038868941000 : ℤ), (-29128357982250 : ℤ)],
        ![(-109423919409000 : ℤ), (245038868941000 : ℤ), (2781173629250 : ℤ), (-33276691482000 : ℤ)],
        ![(-28917389293750 : ℤ), (88900927694000 : ℤ), (-30609857541250 : ℤ), (-9254118013250 : ℤ)]],
      ![![(449036680073414 : ℤ), (-328039072733375 : ℤ), (-109423919409000 : ℤ), (-28917389293750 : ℤ)],
        ![(-328039072733375 : ℤ), (-118044152985500 : ℤ), (245038868941000 : ℤ), (88900927694000 : ℤ)],
        ![(-109423919409000 : ℤ), (245038868941000 : ℤ), (2781173629250 : ℤ), (-30609857541250 : ℤ)],
        ![(87908446464750 : ℤ), (-29128357982250 : ℤ), (-33276691482000 : ℤ), (-9254118013250 : ℤ)]],
      ![![(449036680073414 : ℤ), (-328039072733375 : ℤ), (-109423919409000 : ℤ), (87908446464750 : ℤ)],
        ![(-328039072733375 : ℤ), (-118044152985500 : ℤ), (245038868941000 : ℤ), (-29128357982250 : ℤ)],
        ![(-109423919409000 : ℤ), (245038868941000 : ℤ), (2781173629250 : ℤ), (-33276691482000 : ℤ)],
        ![(87908446464750 : ℤ), (-29128357982250 : ℤ), (-33276691482000 : ℤ), (11701863939250 : ℤ)]]],
    ![
      ![![(468737780275789 : ℤ), (-309629440030125 : ℤ), (-122655223468375 : ℤ), (-37181093218250 : ℤ)],
        ![(-309629440030125 : ℤ), (-155867278585125 : ℤ), (230014293785375 : ℤ), (101416577640625 : ℤ)],
        ![(-122655223468375 : ℤ), (230014293785375 : ℤ), (-5831624831625 : ℤ), (-46592322125875 : ℤ)],
        ![(-37181093218250 : ℤ), (101416577640625 : ℤ), (-46592322125875 : ℤ), (-18985860819125 : ℤ)]],
      ![![(468737780275789 : ℤ), (-309629440030125 : ℤ), (-122655223468375 : ℤ), (85467884391250 : ℤ)],
        ![(-309629440030125 : ℤ), (-155867278585125 : ℤ), (230014293785375 : ℤ), (-17290225324625 : ℤ)],
        ![(-122655223468375 : ℤ), (230014293785375 : ℤ), (-5831624831625 : ℤ), (-17483555531125 : ℤ)],
        ![(-37181093218250 : ℤ), (101416577640625 : ℤ), (-46592322125875 : ℤ), (785362059875 : ℤ)]],
      ![![(468737780275789 : ℤ), (-309629440030125 : ℤ), (-122655223468375 : ℤ), (-37181093218250 : ℤ)],
        ![(-309629440030125 : ℤ), (-155867278585125 : ℤ), (230014293785375 : ℤ), (101416577640625 : ℤ)],
        ![(-122655223468375 : ℤ), (230014293785375 : ℤ), (-5831624831625 : ℤ), (-46592322125875 : ℤ)],
        ![(85467884391250 : ℤ), (-17290225324625 : ℤ), (-17483555531125 : ℤ), (785362059875 : ℤ)]],
      ![![(468737780275789 : ℤ), (-309629440030125 : ℤ), (-122655223468375 : ℤ), (85467884391250 : ℤ)],
        ![(-309629440030125 : ℤ), (-155867278585125 : ℤ), (230014293785375 : ℤ), (-17290225324625 : ℤ)],
        ![(-122655223468375 : ℤ), (230014293785375 : ℤ), (-5831624831625 : ℤ), (-17483555531125 : ℤ)],
        ![(85467884391250 : ℤ), (-17290225324625 : ℤ), (-17483555531125 : ℤ), (4446638841875 : ℤ)]]],
    ![
      ![![(483476811531164 : ℤ), (-302050969146500 : ℤ), (-125452192744625 : ℤ), (-38049270370375 : ℤ)],
        ![(-302050969146500 : ℤ), (-173586034333500 : ℤ), (217902008007375 : ℤ), (100498965574250 : ℤ)],
        ![(-125452192744625 : ℤ), (217902008007375 : ℤ), (-10412496655625 : ℤ), (-48019206112250 : ℤ)],
        ![(-38049270370375 : ℤ), (100498965574250 : ℤ), (-48019206112250 : ℤ), (-19383831921875 : ℤ)]],
      ![![(483476811531164 : ℤ), (-302050969146500 : ℤ), (-125452192744625 : ℤ), (82830456922875 : ℤ)],
        ![(-302050969146500 : ℤ), (-173586034333500 : ℤ), (217902008007375 : ℤ), (-10158386901500 : ℤ)],
        ![(-125452192744625 : ℤ), (217902008007375 : ℤ), (-10412496655625 : ℤ), (-10958247705500 : ℤ)],
        ![(-38049270370375 : ℤ), (100498965574250 : ℤ), (-48019206112250 : ℤ), (2437058984625 : ℤ)]],
      ![![(483476811531164 : ℤ), (-302050969146500 : ℤ), (-125452192744625 : ℤ), (-38049270370375 : ℤ)],
        ![(-302050969146500 : ℤ), (-173586034333500 : ℤ), (217902008007375 : ℤ), (100498965574250 : ℤ)],
        ![(-125452192744625 : ℤ), (217902008007375 : ℤ), (-10412496655625 : ℤ), (-48019206112250 : ℤ)],
        ![(82830456922875 : ℤ), (-10158386901500 : ℤ), (-10958247705500 : ℤ), (2437058984625 : ℤ)]],
      ![![(483476811531164 : ℤ), (-302050969146500 : ℤ), (-125452192744625 : ℤ), (82830456922875 : ℤ)],
        ![(-302050969146500 : ℤ), (-173586034333500 : ℤ), (217902008007375 : ℤ), (-10158386901500 : ℤ)],
        ![(-125452192744625 : ℤ), (217902008007375 : ℤ), (-10412496655625 : ℤ), (-10958247705500 : ℤ)],
        ![(82830456922875 : ℤ), (-10158386901500 : ℤ), (-10958247705500 : ℤ), (2116679895125 : ℤ)]]]]

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
                            Certificate.inside
                            (Certificate.cross (-4346572689884141 : ℤ) (10555311626649600 : ℕ) none)))))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-24 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-4346572689884141 : ℤ) (10555311626649600 : ℕ) none))))
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (-72 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-72 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-285286179280769771951 : ℤ) (691752902764108185600 : ℕ) none)))
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.splitY (-24 : ℤ)
                              (Certificate.cross (-18213197863798006779989 : ℤ) (44272185776902923878400 : ℕ) none)
                              (Certificate.cross (-699884746234524899 : ℤ) (1519964874237542400 : ℕ) none))
                            (Certificate.cross (-142963342176856753 : ℤ) (295548725546188800 : ℕ) none)))
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (-24 : ℤ)
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.cross (-18213197863798006779989 : ℤ) (44272185776902923878400 : ℕ) none)
                              (Certificate.cross (-5671952441054549501983 : ℤ) (12451552249753947340800 : ℕ) none))
                            (Certificate.cross (-142963342176856753 : ℤ) (295548725546188800 : ℕ) none))
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
                          Certificate.inside
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (168 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (156 : ℤ)
                                  Certificate.inside
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (162 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside))
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside))
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          Certificate.inside)))
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
                  (Certificate.cross (-10406098310592629 : ℤ) (15832967439974400 : ℕ) none)))
              (Certificate.cross (-5500848671569001 : ℤ) (8356288371097600 : ℕ) none))
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
                          (Certificate.cross (-844682487663535423 : ℤ) (1351079888211148800 : ℕ) none))))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (48 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-658695960278357173 : ℤ) (1351079888211148800 : ℕ) none)))
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (-383311380005450096951 : ℤ) (691752902764108185600 : ℕ) none)
                          (Certificate.cross (-3500879713596081287 : ℤ) (5404319552844595200 : ℕ) none))
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (-22577000053499333759 : ℤ) (37830236869912166400 : ℕ) none)
                          Certificate.outside))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-450464003113197196451 : ℤ) (691752902764108185600 : ℕ) none)
                          (Certificate.cross (-214578379124305703197 : ℤ) (302641894959297331200 : ℕ) none))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-209811510326030194447 : ℤ) (302641894959297331200 : ℕ) none)
                          Certificate.outside))
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.cross (-302715950100645520451 : ℤ) (691752902764108185600 : ℕ) none)
                          (Certificate.cross (-166152972199843193947 : ℤ) (302641894959297331200 : ℕ) none))
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (-6092598833160240657733 : ℤ) (12451552249753947340800 : ℕ) none)
                            (Certificate.cross (-153982046491734855697 : ℤ) (302641894959297331200 : ℕ) none))
                          Certificate.outside))
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
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (552 : ℤ)
                              Certificate.outside
                              Certificate.outside))))))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
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
                        Certificate.outside)
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
                        Certificate.inside
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (156 : ℤ)
                                Certificate.inside
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (162 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside))
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside))
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
                  (Certificate.cross (-10406098310592629 : ℤ) (15832967439974400 : ℕ) none)))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (48 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-658695960278357173 : ℤ) (1351079888211148800 : ℕ) none)))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-844682487663535423 : ℤ) (1351079888211148800 : ℕ) none)))
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-383311380005450096951 : ℤ) (691752902764108185600 : ℕ) none)
                          (Certificate.cross (-22577000053499333759 : ℤ) (37830236869912166400 : ℕ) none))
                        (Certificate.cross (-951912692143601887 : ℤ) (1463669878895411200 : ℕ) none))))
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-302715950100645520451 : ℤ) (691752902764108185600 : ℕ) none)
                          (Certificate.splitX (24 : ℤ)
                            (Certificate.cross (-734851816205564915201 : ℤ) (1556444031219243417600 : ℕ) none)
                            (Certificate.cross (-153982046491734855697 : ℤ) (302641894959297331200 : ℕ) none)))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-166152972199843193947 : ℤ) (302641894959297331200 : ℕ) none)
                          Certificate.outside))
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.cross (-450464003113197196451 : ℤ) (691752902764108185600 : ℕ) none)
                          (Certificate.cross (-209811510326030194447 : ℤ) (302641894959297331200 : ℕ) none))
                        (Certificate.cross (-8495952534546825221 : ℤ) (11709359031163289600 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-5500848671569001 : ℤ) (8356288371097600 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (552 : ℤ)
                            Certificate.outside
                            Certificate.outside)))))
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (504 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-168 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (624 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    Certificate.outside)
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
                        (Certificate.splitY (48 : ℤ)
                          Certificate.outside
                          Certificate.outside))
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
                                Certificate.outside
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (522 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))))))
                        Certificate.outside))))
                Certificate.outside))))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                Certificate.outside
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
                                  Certificate.outside
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (522 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))))))
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
                            (Certificate.splitY (-312 : ℤ)
                              Certificate.inside
                              Certificate.inside))))
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
                          (Certificate.cross (-2274738052998907 : ℤ) (7036874417766400 : ℕ) none))))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-2274738052998907 : ℤ) (7036874417766400 : ℕ) none))
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-39122126436462926413 : ℤ) (115292150460684697600 : ℕ) none)
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.splitY (-24 : ℤ)
                              (Certificate.cross (-2455169730539748847807 : ℤ) (7378697629483820646400 : ℕ) none)
                              (Certificate.cross (-982245904511565673 : ℤ) (2139209823000985600 : ℕ) none))
                            (Certificate.splitY (-24 : ℤ)
                              (Certificate.cross (-1986096079924647614429 : ℤ) (4381101717506018508800 : ℕ) none)
                              Certificate.outside)))
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (-24 : ℤ)
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.cross (-2455169730539748847807 : ℤ) (7378697629483820646400 : ℕ) none)
                              (Certificate.cross (-1986096079924647614429 : ℤ) (4381101717506018508800 : ℕ) none))
                            (Certificate.cross (-233208099713505131 : ℤ) (478507460408115200 : ℕ) none))
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
                          Certificate.inside
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (168 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (180 : ℤ)
                                  Certificate.inside
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (186 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside))
                                Certificate.inside))
                            Certificate.inside))
                        Certificate.inside))
                    Certificate.inside)
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                Certificate.inside)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.cross (-6575650966949503 : ℤ) (28147497671065600 : ℕ) none)
                      (Certificate.cross (-4912755418071877 : ℤ) (7036874417766400 : ℕ) none)))))
              (Certificate.cross (-5616713187617501 : ℤ) (7916483719987200 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-124464437871214649 : ℤ) (225179981368524800 : ℕ) none))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-93223775535405899 : ℤ) (225179981368524800 : ℕ) none))
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (-55541638668495924913 : ℤ) (115292150460684697600 : ℕ) none)
                          (Certificate.splitX (-264 : ℤ)
                            (Certificate.splitY (168 : ℤ)
                              (Certificate.cross (-3826241014115376111307 : ℤ) (7378697629483820646400 : ℕ) none)
                              (Certificate.cross (-44179329344321841161 : ℤ) (68454714336031539200 : ℕ) none))
                            (Certificate.cross (-10012252256937004567 : ℤ) (15312238733059686400 : ℕ) none)))
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.splitY (120 : ℤ)
                              (Certificate.cross (-3296275144877246043307 : ℤ) (7378697629483820646400 : ℕ) none)
                              (Certificate.cross (-2600379697398231104429 : ℤ) (4381101717506018508800 : ℕ) none))
                            (Certificate.cross (-9283293508851528817 : ℤ) (15312238733059686400 : ℕ) none))
                          Certificate.outside))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-64008273684954965413 : ℤ) (115292150460684697600 : ℕ) none)
                          (Certificate.cross (-87933985830579536411 : ℤ) (122497909864477491200 : ℕ) none))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-312 : ℤ)
                            (Certificate.cross (-3006696346626296017679 : ℤ) (4381101717506018508800 : ℕ) none)
                            (Certificate.cross (-85377451107105429161 : ℤ) (122497909864477491200 : ℕ) none))
                          Certificate.outside))
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.cross (-40854932876497217413 : ℤ) (115292150460684697600 : ℕ) none)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.splitY (72 : ℤ)
                              (Certificate.cross (-2825917342349371320307 : ℤ) (7378697629483820646400 : ℕ) none)
                              (Certificate.cross (-296723223184920642913 : ℤ) (547637714688252313600 : ℕ) none))
                            (Certificate.cross (-68480929006073983661 : ℤ) (122497909864477491200 : ℕ) none)))
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.splitY (24 : ℤ)
                              (Certificate.cross (-2448325326491513526307 : ℤ) (7378697629483820646400 : ℕ) none)
                              (Certificate.cross (-2161655770704240228179 : ℤ) (4381101717506018508800 : ℕ) none))
                            (Certificate.cross (-63203869519377213911 : ℤ) (122497909864477491200 : ℕ) none))
                          Certificate.outside))
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
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (552 : ℤ)
                              Certificate.outside
                              Certificate.outside))))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        Certificate.outside
                        Certificate.outside)
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
                        Certificate.inside
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (168 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (180 : ℤ)
                                Certificate.inside
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (186 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside))
                              Certificate.inside))
                          Certificate.inside))
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
                Certificate.inside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.cross (-6575650966949503 : ℤ) (28147497671065600 : ℕ) none)
                    (Certificate.cross (-4912755418071877 : ℤ) (7036874417766400 : ℕ) none))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (48 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-93223775535405899 : ℤ) (225179981368524800 : ℕ) none)))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (-124464437871214649 : ℤ) (225179981368524800 : ℕ) none)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-55541638668495924913 : ℤ) (115292150460684697600 : ℕ) none)
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.cross (-38848336345328655911 : ℤ) (68454714336031539200 : ℕ) none)
                            (Certificate.cross (-9283293508851528817 : ℤ) (15312238733059686400 : ℕ) none)))
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-2715067638893883149429 : ℤ) (4381101717506018508800 : ℕ) none)
                            (Certificate.cross (-10012252256937004567 : ℤ) (15312238733059686400 : ℕ) none))
                          Certificate.outside))))
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-40854932876497217413 : ℤ) (115292150460684697600 : ℕ) none)
                          (Certificate.splitX (24 : ℤ)
                            (Certificate.cross (-259172147107561642663 : ℤ) (547637714688252313600 : ℕ) none)
                            (Certificate.cross (-63203869519377213911 : ℤ) (122497909864477491200 : ℕ) none)))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (72 : ℤ)
                            (Certificate.cross (-2264305692735859438679 : ℤ) (4381101717506018508800 : ℕ) none)
                            (Certificate.cross (-68480929006073983661 : ℤ) (122497909864477491200 : ℕ) none))
                          Certificate.outside))
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.cross (-64008273684954965413 : ℤ) (115292150460684697600 : ℕ) none)
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.cross (-366244067688303785413 : ℤ) (547637714688252313600 : ℕ) none)
                            (Certificate.cross (-85377451107105429161 : ℤ) (122497909864477491200 : ℕ) none)))
                        (Certificate.cross (-3633423571436566423 : ℤ) (4953959590107545600 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-5616713187617501 : ℤ) (7916483719987200 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (552 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside))))))
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
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
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (624 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside))
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
                        (Certificate.splitY (48 : ℤ)
                          Certificate.outside
                          Certificate.outside))
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
                Certificate.outside
                (Certificate.splitY (1344 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (624 : ℤ)
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (600 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (588 : ℤ)
                                (Certificate.splitY (1524 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (582 : ℤ)
                                    Certificate.outside
                                    Certificate.outside))
                                Certificate.outside))
                            Certificate.outside))
                        Certificate.outside))
                    Certificate.outside))))))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                Certificate.outside
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
                  (Certificate.splitX (1440 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (624 : ℤ)
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (600 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (588 : ℤ)
                                  (Certificate.splitX (1530 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (582 : ℤ)
                                      Certificate.outside
                                      Certificate.outside))
                                  Certificate.outside))
                              Certificate.outside))
                          Certificate.outside))
                      Certificate.outside))))))
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
                        Certificate.inside
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-312 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-312 : ℤ)
                              Certificate.inside
                              Certificate.inside))))
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.splitY (-24 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-269851252419277149 : ℤ) (619244948763443200 : ℕ) none))
                            (Certificate.splitY (-24 : ℤ)
                              (Certificate.cross (-1091630874437321597679 : ℤ) (2536427310135063347200 : ℕ) none)
                              (Certificate.cross (-87793919564638503 : ℤ) (182958734861926400 : ℕ) none))))
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (-24 : ℤ)
                            (Certificate.splitY (-72 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-1091630874437321597679 : ℤ) (2536427310135063347200 : ℕ) none))
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.cross (-269851252419277149 : ℤ) (619244948763443200 : ℕ) none)
                              (Certificate.cross (-87793919564638503 : ℤ) (182958734861926400 : ℕ) none)))
                          (Certificate.cross (-7194223843899 : ℤ) (13743895347200 : ℕ) none))))))))))),
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
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (204 : ℤ)
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (198 : ℤ)
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
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-4371208197226377 : ℤ) (6157265115545600 : ℕ) none)))))
              (Certificate.cross (-1362776415953719 : ℤ) (1869169767219200 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-264 : ℤ)
                            (Certificate.cross (-24671031610556524161 : ℤ) (39631676720860364800 : ℕ) none)
                            (Certificate.splitY (168 : ℤ)
                              (Certificate.cross (-137934145805790342039 : ℤ) (230584300921369395200 : ℕ) none)
                              (Certificate.cross (-7562326630723887567 : ℤ) (11709359031163289600 : ℕ) none))))
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.cross (-1454797674959629623429 : ℤ) (2536427310135063347200 : ℕ) none)
                            (Certificate.splitY (120 : ℤ)
                              (Certificate.cross (-21752765310735744411 : ℤ) (39631676720860364800 : ℕ) none)
                              (Certificate.cross (-7028226658554688317 : ℤ) (11709359031163289600 : ℕ) none)))
                          (Certificate.cross (-843101491495596887 : ℤ) (1294784892869017600 : ℕ) none)))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-66459700109224467411 : ℤ) (93674872249306316800 : ℕ) none))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-312 : ℤ)
                            (Certificate.cross (-1676357247746072366679 : ℤ) (2536427310135063347200 : ℕ) none)
                            (Certificate.cross (-64407219923515039161 : ℤ) (93674872249306316800 : ℕ) none))
                          (Certificate.cross (-30047601447409455259 : ℤ) (41433116571808563200 : ℕ) none)))
                      (Certificate.cross (-128082159051549157 : ℤ) (168884986026393600 : ℕ) none))
                    (Certificate.cross (-801923116234231381 : ℤ) (1069604911500492800 : ℕ) none)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.splitY (72 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-166087137686589785913 : ℤ) (317053413766882918400 : ℕ) none))
                            (Certificate.splitY (72 : ℤ)
                              (Certificate.cross (-1264230001580708105679 : ℤ) (2536427310135063347200 : ℕ) none)
                              (Certificate.cross (-51900295101716036661 : ℤ) (93674872249306316800 : ℕ) none))))
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.splitY (24 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-1200901979205903181179 : ℤ) (2536427310135063347200 : ℕ) none))
                            (Certificate.splitY (24 : ℤ)
                              (Certificate.cross (-143057005953188490663 : ℤ) (317053413766882918400 : ℕ) none)
                              (Certificate.cross (-47789634261751789911 : ℤ) (93674872249306316800 : ℕ) none)))
                          (Certificate.cross (-14398912403067723567 : ℤ) (25220157913274777600 : ℕ) none)))
                      (Certificate.cross (-256314489976803003 : ℤ) (394064967394918400 : ℕ) none))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-60028346310387891 : ℤ) (102034679057612800 : ℕ) none)
                      Certificate.outside))
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
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (552 : ℤ)
                              Certificate.outside
                              Certificate.outside))))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (624 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.splitY (600 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)
                          Certificate.outside))
                      Certificate.outside)))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.splitY (552 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside))
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
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (204 : ℤ)
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (198 : ℤ)
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
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.cross (-4371208197226377 : ℤ) (6157265115545600 : ℕ) none))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.cross (-21752765310735744411 : ℤ) (39631676720860364800 : ℕ) none)
                            (Certificate.cross (-7028226658554688317 : ℤ) (11709359031163289600 : ℕ) none)))
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-137934145805790342039 : ℤ) (230584300921369395200 : ℕ) none)
                            (Certificate.cross (-7562326630723887567 : ℤ) (11709359031163289600 : ℕ) none))
                          (Certificate.cross (-843101491495596887 : ℤ) (1294784892869017600 : ℕ) none)))))
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (24 : ℤ)
                            (Certificate.cross (-143057005953188490663 : ℤ) (317053413766882918400 : ℕ) none)
                            (Certificate.cross (-47789634261751789911 : ℤ) (93674872249306316800 : ℕ) none)))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (72 : ℤ)
                            (Certificate.cross (-1264230001580708105679 : ℤ) (2536427310135063347200 : ℕ) none)
                            (Certificate.cross (-51900295101716036661 : ℤ) (93674872249306316800 : ℕ) none))
                          (Certificate.cross (-14398912403067723567 : ℤ) (25220157913274777600 : ℕ) none)))
                      (Certificate.cross (-60028346310387891 : ℤ) (102034679057612800 : ℕ) none))
                    (Certificate.cross (-256314489976803003 : ℤ) (394064967394918400 : ℕ) none)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.cross (-204436238427344203413 : ℤ) (317053413766882918400 : ℕ) none)
                            (Certificate.cross (-64407219923515039161 : ℤ) (93674872249306316800 : ℕ) none)))
                        (Certificate.cross (-2947545460758488173 : ℤ) (4053239664633446400 : ℕ) none))
                      (Certificate.cross (-18257419604375502567 : ℤ) (25220157913274777600 : ℕ) none))
                    (Certificate.cross (-16408075598649629 : ℤ) (21110623253299200 : ℕ) none))
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-1362776415953719 : ℤ) (1869169767219200 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (552 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside))))))
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (552 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside))
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (624 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (600 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside))
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
                        Certificate.outside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (168 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
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
                          (Certificate.splitX (264 : ℤ)
                            Certificate.outside
                            Certificate.outside))))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (48 : ℤ)
                          Certificate.outside
                          Certificate.outside))
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
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)
                Certificate.outside)
              Certificate.outside))
          (Certificate.splitX (384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              Certificate.outside
              (Certificate.splitX (576 : ℤ)
                Certificate.outside
                (Certificate.splitY (1344 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (672 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (720 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (744 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (756 : ℤ)
                                Certificate.outside
                                Certificate.outside))))))))))))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            Certificate.outside
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                Certificate.outside
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1440 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (720 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (744 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (756 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))))))))))))
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (1152 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                Certificate.outside
                Certificate.outside))
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (1344 : ℤ)
                Certificate.outside
                Certificate.outside)
              Certificate.outside))))],
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
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-312 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-312 : ℤ)
                              Certificate.inside
                              Certificate.inside))))
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.cross (-46035664180610899 : ℤ) (168884986026393600 : ℕ) none)
                            (Certificate.splitY (-24 : ℤ)
                              (Certificate.cross (-381939828842088940733 : ℤ) (1383505805528216371200 : ℕ) none)
                              (Certificate.cross (-55356459197516753 : ℤ) (126663739519795200 : ℕ) none))))
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (-24 : ℤ)
                            (Certificate.cross (-381939828842088940733 : ℤ) (1383505805528216371200 : ℕ) none)
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.cross (-46035664180610899 : ℤ) (168884986026393600 : ℕ) none)
                              (Certificate.cross (-55356459197516753 : ℤ) (126663739519795200 : ℕ) none)))
                          (Certificate.splitX (-24 : ℤ)
                            (Certificate.splitY (-24 : ℤ)
                              (Certificate.cross (-28765961347017868274989 : ℤ) (66408278665354385817600 : ℕ) none)
                              Certificate.outside)
                            Certificate.outside))))))))))),
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
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (228 : ℤ)
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (222 : ℤ)
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
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-7144844202594379 : ℤ) (10555311626649600 : ℕ) none)))))
              (Certificate.cross (-4181601332019563 : ℤ) (5717460464435200 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-264 : ℤ)
                            (Certificate.cross (-10059056299227942197 : ℤ) (21617278211378380800 : ℕ) none)
                            (Certificate.splitY (168 : ℤ)
                              (Certificate.cross (-608171474133867078233 : ℤ) (1383505805528216371200 : ℕ) none)
                              (Certificate.cross (-9706180269313497259 : ℤ) (16212958658533785600 : ℕ) none))))
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.cross (-572693188589325765233 : ℤ) (1383505805528216371200 : ℕ) none)
                            (Certificate.splitY (120 : ℤ)
                              (Certificate.cross (-8427961011563601947 : ℤ) (21617278211378380800 : ℕ) none)
                              (Certificate.cross (-8992398471829556509 : ℤ) (16212958658533785600 : ℕ) none)))
                          (Certificate.cross (-414853838443418131 : ℤ) (675539944105574400 : ℕ) none)))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-84633450634627985447 : ℤ) (129703669268270284800 : ℕ) none))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-312 : ℤ)
                            (Certificate.cross (-669980428867856711483 : ℤ) (1383505805528216371200 : ℕ) none)
                            (Certificate.cross (-82716059636503533197 : ℤ) (129703669268270284800 : ℕ) none))
                          (Certificate.cross (-29575341996908736259 : ℤ) (43234556422756761600 : ℕ) none)))
                      (Certificate.cross (-224761996686859939 : ℤ) (309622474381721600 : ℕ) none))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-1803780400999588956451 : ℤ) (2767011611056432742400 : ℕ) none)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-63303665019668669701 : ℤ) (172938225691027046400 : ℕ) none)
                            (Certificate.splitY (72 : ℤ)
                              (Certificate.cross (-471140225062924952483 : ℤ) (1383505805528216371200 : ℕ) none)
                              (Certificate.cross (-66203013443745289697 : ℤ) (129703669268270284800 : ℕ) none))))
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (-433094583236195931983 : ℤ) (1383505805528216371200 : ℕ) none)
                            (Certificate.splitY (24 : ℤ)
                              (Certificate.cross (-49655892565758312451 : ℤ) (172938225691027046400 : ℕ) none)
                              (Certificate.cross (-60662276318364252947 : ℤ) (129703669268270284800 : ℕ) none)))
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.splitY (72 : ℤ)
                              (Certificate.cross (-32444427745011744605989 : ℤ) (66408278665354385817600 : ℕ) none)
                              Certificate.outside)
                            Certificate.outside)))
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-787207726424136799453 : ℤ) (1383505805528216371200 : ℕ) none)
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.splitY (24 : ℤ)
                              (Certificate.cross (-29851989546060718396489 : ℤ) (66408278665354385817600 : ℕ) none)
                              Certificate.outside)
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))
                  Certificate.outside))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-264 : ℤ)
                            (Certificate.splitY (648 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (648 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (624 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.splitY (600 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)
                          Certificate.outside))
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside))))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)))))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (1152 : ℤ)
              Certificate.outside
              Certificate.outside)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  Certificate.outside)
                Certificate.outside)
              Certificate.outside)))),
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
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (228 : ℤ)
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (222 : ℤ)
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
              Certificate.inside)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.cross (-7144844202594379 : ℤ) (10555311626649600 : ℕ) none))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.cross (-8427961011563601947 : ℤ) (21617278211378380800 : ℕ) none)
                            (Certificate.cross (-8992398471829556509 : ℤ) (16212958658533785600 : ℕ) none)))
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-608171474133867078233 : ℤ) (1383505805528216371200 : ℕ) none)
                            (Certificate.cross (-9706180269313497259 : ℤ) (16212958658533785600 : ℕ) none))
                          (Certificate.cross (-414853838443418131 : ℤ) (675539944105574400 : ℕ) none)))))
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (24 : ℤ)
                            (Certificate.cross (-49655892565758312451 : ℤ) (172938225691027046400 : ℕ) none)
                            (Certificate.splitY (-120 : ℤ)
                              (Certificate.cross (-433094583236195931983 : ℤ) (1383505805528216371200 : ℕ) none)
                              (Certificate.cross (-60662276318364252947 : ℤ) (129703669268270284800 : ℕ) none))))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (72 : ℤ)
                            (Certificate.cross (-471140225062924952483 : ℤ) (1383505805528216371200 : ℕ) none)
                            (Certificate.cross (-66203013443745289697 : ℤ) (129703669268270284800 : ℕ) none))
                          (Certificate.splitX (72 : ℤ)
                            (Certificate.cross (-967229051909042797201 : ℤ) (1902320482601297510400 : ℕ) none)
                            Certificate.outside)))
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (24 : ℤ)
                            (Certificate.cross (-7248507765151332791483 : ℤ) (15218563860810380083200 : ℕ) none)
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.cross (-8344657463340105103733 : ℤ) (15218563860810380083200 : ℕ) none)
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.cross (-83826741383362582201 : ℤ) (172938225691027046400 : ℕ) none)
                            (Certificate.cross (-82716059636503533197 : ℤ) (129703669268270284800 : ℕ) none)))
                        (Certificate.cross (-29575341996908736259 : ℤ) (43234556422756761600 : ℕ) none))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.cross (-68345583893426676893 : ℤ) (104483511354995507200 : ℕ) none)
                        Certificate.outside))
                    (Certificate.cross (-28652113528271633 : ℤ) (38702809297715200 : ℕ) none))
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-4181601332019563 : ℤ) (5717460464435200 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (624 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (600 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (648 : ℤ)
                            (Certificate.splitY (-264 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-264 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (720 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (720 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)))
                  (Certificate.splitX (672 : ℤ)
                    Certificate.outside
                    Certificate.outside))))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (864 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
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
                        Certificate.outside
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
                          (Certificate.splitX (216 : ℤ)
                            Certificate.outside
                            Certificate.outside))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.outside
                            Certificate.outside)
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
          Certificate.outside)
        (Certificate.splitY (768 : ℤ)
          Certificate.outside
          (Certificate.splitX (1152 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1248 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1296 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1320 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1308 : ℤ)
                                Certificate.outside
                                Certificate.outside))
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              Certificate.outside)))))))
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1248 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1296 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1320 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (1308 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside))))))
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (1392 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1392 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      (Certificate.splitX (1392 : ℤ)
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (1392 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))))))))],
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
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-312 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-312 : ℤ)
                              Certificate.inside
                              Certificate.inside))))
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-72 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-24 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-56541434804314131 : ℤ) (140737488355328000 : ℕ) none))))
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (-24 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-56541434804314131 : ℤ) (140737488355328000 : ℕ) none))
                          (Certificate.splitX (-24 : ℤ)
                            (Certificate.splitY (-24 : ℤ)
                              (Certificate.cross (-14663342654285384891739 : ℤ) (36893488147419103232000 : ℕ) none)
                              (Certificate.cross (-1279032673221205923 : ℤ) (2814749767106560000 : ℕ) none))
                            (Certificate.cross (-16569750589209 : ℤ) (34359738368000 : ℕ) none)))))))))))),
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
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (228 : ℤ)
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (222 : ℤ)
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
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-5674664242428129 : ℤ) (8796093022208000 : ℕ) none)))))
              (Certificate.cross (-7927719941739251 : ℤ) (10995116277760000 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-5055953332913638509 : ℤ) (9007199254740992000 : ℕ) none))
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-4681744957105880259 : ℤ) (9007199254740992000 : ℕ) none))
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.splitY (168 : ℤ)
                              (Certificate.cross (-19930382668400664517239 : ℤ) (36893488147419103232000 : ℕ) none)
                              (Certificate.cross (-106491182880413186697 : ℤ) (180143985094819840000 : ℕ) none))
                            (Certificate.cross (-337069456007716881 : ℤ) (562949953421312000 : ℕ) none))))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.cross (-43179196943906656197 : ℤ) (72057594037927936000 : ℕ) none)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-43192481234477409447 : ℤ) (72057594037927936000 : ℕ) none)
                          (Certificate.cross (-24003371756982177009 : ℤ) (36028797018963968000 : ℕ) none)))
                      (Certificate.cross (-200077676273364689 : ℤ) (281474976710656000 : ℕ) none))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-264 : ℤ)
                            (Certificate.cross (-7252494348836081449983 : ℤ) (11529215046068469760000 : ℕ) none)
                            (Certificate.cross (-1464270104115957489201 : ℤ) (2305843009213693952000 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-168 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (72 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-34559812700438926947 : ℤ) (72057594037927936000 : ℕ) none))))
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.splitX (-120 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (24 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-31474337672691578697 : ℤ) (72057594037927936000 : ℕ) none)))
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.splitY (72 : ℤ)
                              (Certificate.cross (-16916093955305723707239 : ℤ) (36893488147419103232000 : ℕ) none)
                              (Certificate.cross (-741126019064545483701 : ℤ) (1441151880758558720000 : ℕ) none))
                            (Certificate.cross (-19005899196093462009 : ℤ) (36028797018963968000 : ℕ) none))))
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.splitY (120 : ℤ)
                              (Certificate.cross (-18440483926911520718739 : ℤ) (36893488147419103232000 : ℕ) none)
                              (Certificate.cross (-6368205200651802719733 : ℤ) (11529215046068469760000 : ℕ) none))
                            (Certificate.cross (-1296977209459169739201 : ℤ) (2305843009213693952000 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.splitY (24 : ℤ)
                              (Certificate.cross (-15362439710697774002739 : ℤ) (36893488147419103232000 : ℕ) none)
                              (Certificate.cross (-5512288766491696470483 : ℤ) (11529215046068469760000 : ℕ) none))
                            (Certificate.cross (-1146159926536144164201 : ℤ) (2305843009213693952000 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))
                  Certificate.outside))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (720 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-264 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (648 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (720 : ℤ)
                          (Certificate.splitX (-264 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside))))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)))))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (1152 : ℤ)
              Certificate.outside
              Certificate.outside)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  Certificate.outside)
                Certificate.outside)
              Certificate.outside)))),
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
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (228 : ℤ)
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (222 : ℤ)
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
              Certificate.inside)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.cross (-5674664242428129 : ℤ) (8796093022208000 : ℕ) none))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (120 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-4681744957105880259 : ℤ) (9007199254740992000 : ℕ) none)))
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-5055953332913638509 : ℤ) (9007199254740992000 : ℕ) none)
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-102978822563007720447 : ℤ) (180143985094819840000 : ℕ) none)
                            (Certificate.cross (-337069456007716881 : ℤ) (562949953421312000 : ℕ) none))))))
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (24 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-31474337672691578697 : ℤ) (72057594037927936000 : ℕ) none)))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (72 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-34559812700438926947 : ℤ) (72057594037927936000 : ℕ) none))
                          (Certificate.splitX (72 : ℤ)
                            (Certificate.splitY (-120 : ℤ)
                              (Certificate.cross (-16916093955305723707239 : ℤ) (36893488147419103232000 : ℕ) none)
                              (Certificate.cross (-714267489595646930451 : ℤ) (1441151880758558720000 : ℕ) none))
                            (Certificate.cross (-19005899196093462009 : ℤ) (36028797018963968000 : ℕ) none))))
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (24 : ℤ)
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.cross (-15362439710697774002739 : ℤ) (36893488147419103232000 : ℕ) none)
                              (Certificate.cross (-5342750222017147492233 : ℤ) (11529215046068469760000 : ℕ) none))
                            (Certificate.cross (-1146159926536144164201 : ℤ) (2305843009213693952000 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.cross (-6147852875406732034983 : ℤ) (11529215046068469760000 : ℕ) none)
                            (Certificate.cross (-1296977209459169739201 : ℤ) (2305843009213693952000 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.cross (-43192481234477409447 : ℤ) (72057594037927936000 : ℕ) none)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.cross (-43179196943906656197 : ℤ) (72057594037927936000 : ℕ) none)
                          (Certificate.cross (-24003371756982177009 : ℤ) (36028797018963968000 : ℕ) none)))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.cross (-7039324341299314952733 : ℤ) (11529215046068469760000 : ℕ) none)
                            (Certificate.cross (-1464270104115957489201 : ℤ) (2305843009213693952000 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.cross (-25507853194470133 : ℤ) (35184372088832000 : ℕ) none))
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-7927719941739251 : ℤ) (10995116277760000 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (624 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (648 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-264 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (720 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (720 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (696 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside)))
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside))))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (864 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
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
                      (Certificate.splitX (144 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
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
                          (Certificate.splitX (216 : ℤ)
                            Certificate.outside
                            Certificate.outside))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.outside
                            Certificate.outside)
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

end BerryEsseen.N2NeededIntegerPointwise07

#print axioms BerryEsseen.N2NeededIntegerPointwise07.powers_entries
#print axioms BerryEsseen.N2NeededIntegerPointwise07.powers_eq
#print axioms BerryEsseen.N2NeededIntegerPointwise07.checks
#print axioms BerryEsseen.N2NeededIntegerPointwise07.pointwise
