package hx25519;

import haxe.Int32;
import haxe.io.Bytes;

@:forward
abstract Vec(haxe.ds.Vector< Int32 >)
{
	public function new() {
		this = new haxe.ds.Vector(32);
	}

	public static function make_zero()
	{
		var r = new Vec();
		for (i in 0 ... 32) r.setV(i, 0);
		return r;
	}

	public static function make_one()
	{
		var r = new Vec();
		for (i in 1 ... 32) r.setV(i, 0);
		r.setV(0, 1);
		return r;
	}

	public static function make_a24()
	{
		//0x1DB41;

		var r = new Vec();
		for (i in 1 ... 32) r.setV(i, 0);
		r.set(0, 0x41);
		r.set(1, 0xDB);
		r.set(2, 0x01);
		return r;
	}

	inline public function getV(i : Int) : Int32 return this.get(i);
	inline public function setV(i : Int, v : Int32) { this.set(i, v); }

	public function copy(x : Vec) {
		for (i in 0 ... 32) setV(i, x.getV(i));
	}

	public function small(x : Int) {
		for (i in 1 ... 32) this.set(i, 0);
		this.set(0, x);

		vnorm();
	}

	// Functions bellow assume `this` will store the result

	//### need to unroll these loops!
	public function vadd(a : Vec, b : Vec) {
		for (i in 0 ... 32)
			this.set(i, a.get(i) + b.get(i));
	}

	public function vsub(a : Vec, b : Vec) {
		for (i in 0 ... 32)
			this.set(i, a.get(i) - b.get(i));
	}

	public function vmult(a : Vec, b : Vec) {
		var v : Int32;
		for (i in 0 ... 32) {
			v = 0;
			var j = 0;
			while (j <= i) {
				v += a.getV(j) * b.getV(i - j);
				++j;
			}
			j = i + 1;
			while (j < 32) {
				v += 38 * a.getV(j) * b.getV(i + 32 - j);
				++j;
			}
			setV(i, v);
		}

		vnorm();
		vnorm();
	}

	public function vsqr(a : Vec) { vmult(a, a); }

	static var _a24 = Vec.make_a24();

	public function vmult_121665(a : Vec)
	{
#if 0
		var v : Int32 = 0;
		for (j in 0 ... 31) {
			v += 121665 * a.getV(j);
			setV(j, v & 255);
			v >>= 8;
		}
		v += 121665 * a.getV(31);
		setV(31, v & 127);
#else
		vmult(a, _a24);
#end

		vnorm();
		vnorm();
	}

	public function vnorm()
	{
		var v : Int32 = 0;
		for (j in 0 ... 31) {
			v = getV(j) + (1 << 8);
			var c = v >> 8;

			setV(j + 1, getV(j + 1) + (c - 1));
			setV(j, v - (c << 8));
		}

		v = getV(31) + (1 << 8);
		var c = v >> 8;
		setV(0, getV(0) + 38 * (c - 1));
		setV(31, v - (c << 8));
	}

	public function freeze(temp: Vec) {
		vnorm();

		var v : Int32 = this.get(31);
		var x = v >>> 7;
		this.set(31, v & 0x7f);
		v = x * 19;
		for (j in 0 ... 31) {
			v += getV(j);
			this.set(j, v & 255);
			v >>>= 8;
		}
		v += getV(31);
		setV(31, v);
	}
}


/**
 *  Curve25519 DH key exchange algorithm.
 *  
 *  This implementation is designed to be fast and secure against
 *  side channel attacks. This implementation does not include signature 
 *  scheme. It can however be extended to EC
 */
class Hx25519
{
	// Part of the ladder for doubling
	//  x + z     x - z
	//    |         |
	//   ^2        ^2
	//    |---. .---|
	//    |    X    |
	//   (*)<-' :->(-) ---.
	//    |     |   |     |
	//    |     |  (*) <--|-- a24
	//    |     |   |     |
	//    |     '->(+)    |
	//    |         |     |
	//    |        (*) <--'
	//    |         |
	//    v         v
	// 
	//    X         Z
	//
	// - this function destroys contents of tx, ty
	static function pt_double(rx : Vec, rz : Vec, ax : Vec, az : Vec, tx : Vec, tz : Vec)
	{
		//### there should be more efficient formula for squaring
		tx.vmult(ax, ax);
		tz.vmult(az, az);

		rx.vmult(tx, tz);

		tz.vsub(tx, tz);
		rz.vmult_121665(tz);
		tx.vadd(tx, rz);
		rz.vmult(tx, tz);
	}

	// Part of the ladder for addition
	//           x1 + z1   x1 - z1
	//              |         |
	// x2 - z2 --> (*)       (*) <-- x2 + z2
	//              |---. .---|
	//              |    X    |
	//             (+)<-' '->(-)
	//              |         | 
	//             ^2        ^2
	//              |         |
	//              |        (*) <-- dx
	//              |         |
	//              v         v
	//           
	//              X         Z
	//
	// - this function destroys contents of ax & az
	static function pt_add(rx : Vec, rz : Vec, ax : Vec, az : Vec, bx : Vec, bz : Vec, dx : Vec)
	{
		//### there should be more efficient formula for squaring
		rx.vmult(ax, bz);
		rz.vmult(az, bx);

		ax.vadd(rx, rz);
		az.vsub(rx, rz);

		rx.vmult(ax, ax);
		ax.vmult(az, az);

		rz.vmult(ax, dx);
	}

	// Top part of each side of the ladder
	//
	// rx = ax + az
	// ry = ax - az
	static function pt_diffs(rx : Vec, rz: Vec, ax : Vec, az : Vec)
	{
		rx.vadd(ax, az);
		rz.vsub(ax, az);
	}

	//------------------------------------------
	static function cond_swap(x1 : Vec, x2 : Vec, b : Int32)
	{
		var mn : Int32 = (b - 1) & 0xFFFFFFFF; // b=1 => 0 / b=0 => ~0
		var mp : Int32 = (~mn) & 0xFFFFFFFF;

		for (i in 0 ... 32) {
			var a = x1.getV(i);
			var b = x2.getV(i);

			var tx = (a ^ b) & mp;
			
			x1.setV(i, a ^ tx);
			x2.setV(i, b ^ tx);
		}
	}

	static function recip(z : Vec, t0 : Vec, t1 : Vec, t2 : Vec, t3 : Vec, t4 : Vec) {

		/* the chain for z^(2^255-21) is straight from djb's implementation */
		t1.vsqr(z);				//  2 == 2 * 1
		t2.vsqr(t1);			//  4 == 2 * 2
		t0.vsqr(t2);			//  8 == 2 * 4
		t2.vmult(t0, z);		//  9 == 8 + 1
		t0.vmult(t2, t1);		// 11 == 9 + 2
		t1.vsqr(t0);			// 22 == 2 * 11
		t3.vmult(t1, t2);		// 31 == 22 + 9 == 2^5   - 2^0
		t1.vsqr(t3);			// 2^6   - 2^1
		t2.vsqr(t1);			// 2^7   - 2^2
		t1.vsqr(t2);			// 2^8   - 2^3
		t2.vsqr(t1);			// 2^9   - 2^4
		t1.vsqr(t2);			// 2^10  - 2^5
		t2.vmult(t1, t3);		// 2^10  - 2^0
		t1.vsqr(t2);			// 2^11  - 2^1
		t3.vsqr(t1);			// 2^12  - 2^2

		for (i in 1 ... 5) {
			t1.vsqr(t3);
			t3.vsqr(t1);
		}						// 2^20  - 2^10
		t1.vmult(t3, t2);		// 2^20  - 2^0	
		t3.vsqr(t1);			// 2^21  - 2^1
		t4.vsqr(t3);			// 2^22  - 2^2
		for (i in 1 ... 10) {
			t3.vsqr(t4);
			t4.vsqr(t3);
		}						// 2^40  - 2^20
		t3.vmult(t4, t1);		// 2^40  - 2^0
		for (i in 0 ... 5) {
			t1.vsqr(t3);
			t3.vsqr(t1);
		}						// 2^50  - 2^10
		t1.vmult(t3, t2);		// 2^50  - 2^0
		t2.vsqr(t1);			// 2^51  - 2^1
		t3.vsqr(t2);			// 2^52  - 2^2
		for (i in 1 ... 25) {
			t2.vsqr(t3);
			t3.vsqr(t2);
		}						// 2^100 - 2^50
		t2.vmult(t3, t1);		// 2^100 - 2^0
		t3.vsqr(t2);			// 2^101 - 2^1
		t4.vsqr(t3);			// 2^102 - 2^2
		for (i in 1 ... 50) {
			t3.vsqr(t4);
			t4.vsqr(t3);
		}						// 2^200 - 2^100
		t3.vmult(t4, t2);		// 2^200 - 2^0
		for (i in 0 ... 25) {
			t4.vsqr(t3);
			t3.vsqr(t4);
		}						// 2^250 - 2^50
		t2.vmult(t3, t1);		// 2^250 - 2^0
		t1.vsqr(t2);			// 2^251 - 2^1
		t2.vsqr(t1);			// 2^252 - 2^2

		t1.vsqr(t2);			// 2^253 - 2^3
		t2.vsqr(t1);			// 2^254 - 2^4
		t1.vsqr(t2);			// 2^255 - 2^5
		z.vmult(t1, t0);		// 2^255 - 21
	}

	static function curve25519(result : Bytes, multiplier : Bytes, base : Bytes)
	{
		var e = Bytes.alloc(32);
		e.blit(0, multiplier, 0, 32);

		e.set(0, e.get(0) & 248);
		e.set(31, (e.get(31) & 127) | 64);
		
		var px = Vec.make_one();
		var pz = Vec.make_zero();
		var qx = new Vec();
		var qz = Vec.make_one();

		// expand base into Qx
		if (base == null) {
			// basepoint for key generator
			// always x = 9
			qx.small(9);
		} else {
			// unpack bytes into array of int32
			for (i in 0 ... 32) {
				qx.setV(i, base.get(i));
			}
		}

		var dx = new Vec();
		dx.copy(qx);

		var t0 = new Vec();
		var t1 = new Vec();
		var t2 = new Vec();
		var t3 = new Vec();


		// Montgomery ladder
		//
		// R0 = Zero (x = 0, z = 1)
		// R1 = P    (x = e, z = 1)

		// Main loop
		var y = e.length - 1;
		while (y >= 0) {
			var yy = e.get(y);

			var bm = 8;
			while ((--bm) >= 0) {
				var b = (yy >> 7) & 1;
				
				yy <<= 1;

				//### make this cond-swap later
				// depending on bit we need to do one of two operations
				//	if (b == 0) {
				//		Q = pt_add(P, Q)
				//		P = pt_double(P)
				//	} else {
				//		P = pt_add(P, Q)
				//		Q = pt_double(Q)
				//	}

				cond_swap(px, qx, b);
				cond_swap(pz, qz, b);

				pt_diffs(t0, t1, qx, qz);
				pt_diffs(t2, t3, px, pz);

				if (y > 32) {
					traceHex("t2", t2);
					traceHex("t3", t3);
					traceHex("t0", t0);
					traceHex("t1", t1);
				}

				pt_add(qx, qz, t0, t1, t2, t3, dx);
				pt_double(px, pz, t2, t3, t0, t1);

				if (y > 32) {
					traceHex("px", px);
					traceHex("pz", pz);
					traceHex("qx", qx);
					traceHex("qz", qz);
					trace("----");
				}

				cond_swap(px, qx, b);
				cond_swap(pz, qz, b);
			}

			--y;
		}

		traceHex("px", px);
		traceHex("pz", pz);
		traceHex("qx", qx);
		traceHex("qz", qz);

		// finalize
		recip(pz, t0, t1, t2, t3, qz); // compute inverse of z coordinate
		qx.vmult(px, pz); // scale x with z
		qx.freeze(px);

		for (i in 0 ... 32) {
			result.set(i, qx.getV(i));
		}
	}

	public static function genKeypair(secretKey : Bytes)
	{
		var sharedKey = haxe.io.Bytes.alloc(32);

		curve25519(sharedKey, secretKey, null);
		return sharedKey;
	}

	public static function combineKeys(secretKey : Bytes, publicKey : Bytes)
	{
		if (secretKey != null && secretKey.length != 32) throw "Bad secretKey length";
		if (publicKey != null && publicKey.length != 32) throw "Bad publicKey length";

		var sharedKey = haxe.io.Bytes.alloc(32);

		curve25519(sharedKey, secretKey, publicKey);
		return sharedKey;
	}

	static inline function traceHex(name : String, x : Vec)
	{
#if 0
		var s = new StringBuf();

		for (i in 0 ... x.length) {
			s.add(StringTools.hex(x.get(i), 2));
			s.add(" ");
		}

		trace('$name => ${s.toString()}');
#end
	}
}