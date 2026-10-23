import Collatz.MCycle110Certs42

/-!
# Certificates of the listed shapes of `data110`, chunks 168..171
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_168 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_168 = true := by
  decide +kernel

theorem certs110_169 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_169 = true := by
  decide +kernel

theorem certs110_170 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_170 = true := by
  decide +kernel

theorem certs110_171 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_171 = true := by
  decide +kernel

end Collatz
