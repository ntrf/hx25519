package tests;

import haxe.io.Bytes;

class TestCurve
{
	static function printKey(name : String, x : Bytes)
	{
		var s = new StringBuf();

		for (i in 0 ... x.length) {
			s.add(StringTools.hex(x.get(i), 2));
			s.add(" ");
		}

		trace('Key $name => ${s.toString()}');
	}

	static public function main()
	{
		var key1 = Bytes.alloc(32);
		var key2 = Bytes.alloc(32);

		var key1_data = 
		[0x6A,0x2C,0xB9,0x1D, 0xA5,0xFB,0x77,0xB1,
		0x2A,0x99,0xC0,0xEB, 0x87,0x2F,0x4C,0xDF,
        0x45,0x66,0xB2,0x51, 0x72,0xC1,0x16,0x3C,
		0x7D,0xA5,0x18,0x73, 0x0A,0x6D,0x07,0x70];

		var key2_data = 
		[0x6B,0xE0,0x88,0xFF,0x27,0x8B,0x2F,0x1C,0xFD,0xB6,0x18,0x26,0x29,0xB1,0x3B,0x6F,
        0xE6,0x0E,0x80,0x83,0x8B,0x7F,0xE1,0x79,0x4B,0x8A,0x4A,0x62,0x7E,0x08,0xAB,0x58];

		var index = 0;

		while (index < 10) {

			index++;

			for (i in 0 ... 32) {
				key1.set(i, Std.random(256));
				key2.set(i, Std.random(256));
				//key1.set(i, key1_data[31 - i]);
				//key2.set(i, key2_data[31 - i]);
			}

			var pk1 = hx25519.Hx25519.genKeypair(key1);
			var pk2 = hx25519.Hx25519.genKeypair(key2);

			var sk1 = hx25519.Hx25519.combineKeys(key1, pk2);
			var sk2 = hx25519.Hx25519.combineKeys(key2, pk1);

			var i = sk1.compare(sk2);

			if (i != 0) {
				printKey("Private key 1", key1);
				printKey("Private key 2", key2);

				printKey("Public key 1", pk1);
				printKey("Public key 2", pk2);

				printKey("Shared key 1", sk1);
				printKey("Shared key 2", sk2);

				trace('attempt #$index : MISSMATCH');
				break;
			} else {
				//trace("-------- OK ---------");
			}

			trace('attempt #$index : OK');

			Sys.sleep(0.02);
		}
	}
}