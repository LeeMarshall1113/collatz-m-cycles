import Collatz.MCycle110Certs53

/-!
# Certificates of the listed shapes of `data110`, chunks 212..215
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_212 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_212 = true := by
  decide +kernel

theorem certs110_213 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_213 = true := by
  decide +kernel

theorem certs110_214 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_214 = true := by
  decide +kernel

theorem certs110_215 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_215 = true := by
  decide +kernel

end Collatz
