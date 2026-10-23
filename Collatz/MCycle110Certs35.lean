import Collatz.MCycle110Certs34

/-!
# Certificates of the listed shapes of `data110`, chunks 136..139
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_136 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_136 = true := by
  decide +kernel

theorem certs110_137 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_137 = true := by
  decide +kernel

theorem certs110_138 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_138 = true := by
  decide +kernel

theorem certs110_139 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_139 = true := by
  decide +kernel

end Collatz
