package Octets is
   pragma Pure;

   Bits : constant := 8;

   type T is range 0 .. 255;
   for T'Size use Bits;

end Octets;
