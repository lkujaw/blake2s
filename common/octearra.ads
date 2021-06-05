with Octets;

--# inherit Octets;
package Octet_Arrays is
   pragma Pure;

   type T is array (Positive range <>) of Octets.T;
   pragma Pack (T);

end Octet_Arrays;
