import Collatz.MCycle110Certs47

/-!
# Certificates of the listed shapes of `data110`, chunks 188..191
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_188 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_188 = true := by
  decide +kernel

theorem certs110_189 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_189 = true := by
  decide +kernel

theorem certs110_190 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_190 = true := by
  decide +kernel

theorem certs110_191 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_191 = true := by
  decide +kernel

end Collatz
