import Collatz.MCycle110Certs43

/-!
# Certificates of the listed shapes of `data110`, chunks 172..175
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_172 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_172 = true := by
  decide +kernel

theorem certs110_173 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_173 = true := by
  decide +kernel

theorem certs110_174 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_174 = true := by
  decide +kernel

theorem certs110_175 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_175 = true := by
  decide +kernel

end Collatz
