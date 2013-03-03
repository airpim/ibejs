/*
 * ibejs - Identity Based Encryption Javascript library.  
 *
 * Copyright (C) <2013 airpim srl> Tiziano Tresanti <info@airpim.com>
 * 
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Affero General Public License for more details.
 * 
 * You should have received a copy of the GNU Affero General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/."
 */

//Identity Based Encryption(IBE)and decryption in javascript
//IBE is a form of public-key encryption where the public key is actually a common string.
//using Boneh-Franklin scheme
//by Daniel Cheng 
//Email:dongxucheng@gmail.com
//
//dependencies:
// 1.Big Integer Library v. 5.4
// 	Leemon Baird
// 	www.leemon.com
//
// 2. SHA512 http://www.happycode.info/
//	http://jssha.sourceforge.net/
//
//The encrpytion and decryption interface is:
//function ibe_encrypt(id,msg)
//function ibe_decrypt(secretKeyJson,msgJson)
//in ibe.js
//
//the secret key extraction function is :
//function extract_secret_key(id)
//in ibe_extract.js
//notice: keep this function at your PKG server. don't let the client know it.
//
//

////////////////////////////////////////////////////////////////////////////////////////
// Big Integer Library v. 5.4
// Created 2000, last modified 2009
// Leemon Baird
// www.leemon.com
//
// Version history:
// v 5.4  3 Oct 2009
//   - added "var i" to greaterShift() so i is not global. (Thanks to P巘er Szab� for finding that bug)
//
// v 5.3  21 Sep 2009
//   - added randProbPrime(k) for probable primes
//   - unrolled loop in mont_ (slightly faster)
//   - millerRabin now takes a bigInt parameter rather than an int
//
// v 5.2  15 Sep 2009
//   - fixed capitalization in call to int2bigInt in randBigInt
//     (thanks to Emili Evripidou, Reinhold Behringer, and Samuel Macaleese for finding that bug)
//
// v 5.1  8 Oct 2007 
//   - renamed inverseModInt_ to inverseModInt since it doesn't change its parameters
//   - added functions GCD and randBigInt, which call GCD_ and randBigInt_
//   - fixed a bug found by Rob Visser (see comment with his name below)
//   - improved comments
//
// This file is public domain.   You can use it for any purpose without restriction.
// I do not guarantee that it is correct, so use it at your own risk.  If you use 
// it for something interesting, I'd appreciate hearing about it.  If you find 
// any bugs or make any improvements, I'd appreciate hearing about those too.
// It would also be nice if my name and URL were left in the comments.  But none 
// of that is required.
//
// This code defines a bigInt library for arbitrary-precision integers.
// A bigInt is an array of integers storing the value in chunks of bpe bits, 
// little endian (buff[0] is the least significant word).
// Negative bigInts are stored two's complement.  Almost all the functions treat
// bigInts as nonnegative.  The few that view them as two's complement say so
// in their comments.  Some functions assume their parameters have at least one 
// leading zero element. Functions with an underscore at the end of the name put
// their answer into one of the arrays passed in, and have unpredictable behavior 
// in case of overflow, so the caller must make sure the arrays are big enough to 
// hold the answer.  But the average user should never have to call any of the 
// underscored functions.  Each important underscored function has a wrapper function 
// of the same name without the underscore that takes care of the details for you.  
// For each underscored function where a parameter is modified, that same variable 
// must not be used as another argument too.  So, you cannot square x by doing 
// multMod_(x,x,n).  You must use squareMod_(x,n) instead, or do y=dup(x); multMod_(x,y,n).
// Or simply use the multMod(x,x,n) function without the underscore, where
// such issues never arise, because non-underscored functions never change
// their parameters; they always allocate new memory for the answer that is returned.
//
// These functions are designed to avoid frequent dynamic memory allocation in the inner loop.
// For most functions, if it needs a BigInt as a local variable it will actually use
// a global, and will only allocate to it only when it's not the right size.  This ensures
// that when a function is called repeatedly with same-sized parameters, it only allocates
// memory on the first call.
//
// Note that for cryptographic purposes, the calls to Math.random() must 
// be replaced with calls to a better pseudorandom number generator.
//
// In the following, "bigInt" means a bigInt with at least one leading zero element,
// and "integer" means a nonnegative integer less than radix.  In some cases, integer 
// can be negative.  Negative bigInts are 2s complement.
// 
// The following functions do not modify their inputs.
// Those returning a bigInt, string, or Array will dynamically allocate memory for that value.
// Those returning a boolean will return the integer 0 (false) or 1 (true).
// Those returning boolean or int will not allocate memory except possibly on the first 
// time they're called with a given parameter size.
// 
// bigInt  add(x,y)               //return (x+y) for bigInts x and y.  
// bigInt  addInt(x,n)            //return (x+n) where x is a bigInt and n is an integer.
// string  bigInt2str(x,base)     //return a string form of bigInt x in a given base, with 2 <= base <= 95
// int     bitSize(x)             //return how many bits long the bigInt x is, not counting leading zeros
// bigInt  dup(x)                 //return a copy of bigInt x
// boolean equals(x,y)            //is the bigInt x equal to the bigint y?
// boolean equalsInt(x,y)         //is bigint x equal to integer y?
// bigInt  expand(x,n)            //return a copy of x with at least n elements, adding leading zeros if needed
// Array   findPrimes(n)          //return array of all primes less than integer n
// bigInt  GCD(x,y)               //return greatest common divisor of bigInts x and y (each with same number of elements).
// boolean greater(x,y)           //is x>y?  (x and y are nonnegative bigInts)
// boolean greaterShift(x,y,shift)//is (x <<(shift*bpe)) > y?
// bigInt  int2bigInt(t,n,m)      //return a bigInt equal to integer t, with at least n bits and m array elements
// bigInt  inverseMod(x,n)        //return (x**(-1) mod n) for bigInts x and n.  If no inverse exists, it returns null
// int     inverseModInt(x,n)     //return x**(-1) mod n, for integers x and n.  Return 0 if there is no inverse
// boolean isZero(x)              //is the bigInt x equal to zero?
// boolean millerRabin(x,b)       //does one round of Miller-Rabin base integer b say that bigInt x is possibly prime? (b is bigInt, 1<b<x)
// boolean millerRabinInt(x,b)    //does one round of Miller-Rabin base integer b say that bigInt x is possibly prime? (b is int,    1<b<x)
// bigInt  mod(x,n)               //return a new bigInt equal to (x mod n) for bigInts x and n.
// int     modInt(x,n)            //return x mod n for bigInt x and integer n.
// bigInt  mult(x,y)              //return x*y for bigInts x and y. This is faster when y<x.
// bigInt  multMod(x,y,n)         //return (x*y mod n) for bigInts x,y,n.  For greater speed, let y<x.
// boolean negative(x)            //is bigInt x negative?
// bigInt  powMod(x,y,n)          //return (x**y mod n) where x,y,n are bigInts and ** is exponentiation.  0**0=1. Faster for odd n.
// bigInt  randBigInt(n,s)        //return an n-bit random BigInt (n>=1).  If s=1, then the most significant of those n bits is set to 1.
// bigInt  randTruePrime(k)       //return a new, random, k-bit, true prime bigInt using Maurer's algorithm.
// bigInt  randProbPrime(k)       //return a new, random, k-bit, probable prime bigInt (probability it's composite less than 2^-80).
// bigInt  str2bigInt(s,b,n,m)    //return a bigInt for number represented in string s in base b with at least n bits and m array elements
// bigInt  sub(x,y)               //return (x-y) for bigInts x and y.  Negative answers will be 2s complement
// bigInt  trim(x,k)              //return a copy of x with exactly k leading zero elements
//
//
// The following functions each have a non-underscored version, which most users should call instead.
// These functions each write to a single parameter, and the caller is responsible for ensuring the array 
// passed in is large enough to hold the result. 
//
// void    addInt_(x,n)          //do x=x+n where x is a bigInt and n is an integer
// void    add_(x,y)             //do x=x+y for bigInts x and y
// void    copy_(x,y)            //do x=y on bigInts x and y
// void    copyInt_(x,n)         //do x=n on bigInt x and integer n
// void    GCD_(x,y)             //set x to the greatest common divisor of bigInts x and y, (y is destroyed).  (This never overflows its array).
// boolean inverseMod_(x,n)      //do x=x**(-1) mod n, for bigInts x and n. Returns 1 (0) if inverse does (doesn't) exist
// void    mod_(x,n)             //do x=x mod n for bigInts x and n. (This never overflows its array).
// void    mult_(x,y)            //do x=x*y for bigInts x and y.
// void    multMod_(x,y,n)       //do x=x*y  mod n for bigInts x,y,n.
// void    powMod_(x,y,n)        //do x=x**y mod n, where x,y,n are bigInts (n is odd) and ** is exponentiation.  0**0=1.
// void    randBigInt_(b,n,s)    //do b = an n-bit random BigInt. if s=1, then nth bit (most significant bit) is set to 1. n>=1.
// void    randTruePrime_(ans,k) //do ans = a random k-bit true random prime (not just probable prime) with 1 in the msb.
// void    sub_(x,y)             //do x=x-y for bigInts x and y. Negative answers will be 2s complement.
//
// The following functions do NOT have a non-underscored version. 
// They each write a bigInt result to one or more parameters.  The caller is responsible for
// ensuring the arrays passed in are large enough to hold the results. 
//
// void addShift_(x,y,ys)       //do x=x+(y<<(ys*bpe))
// void carry_(x)               //do carries and borrows so each element of the bigInt x fits in bpe bits.
// void divide_(x,y,q,r)        //divide x by y giving quotient q and remainder r
// int  divInt_(x,n)            //do x=floor(x/n) for bigInt x and integer n, and return the remainder. (This never overflows its array).
// int  eGCD_(x,y,d,a,b)        //sets a,b,d to positive bigInts such that d = GCD_(x,y) = a*x-b*y
// void halve_(x)               //do x=floor(|x|/2)*sgn(x) for bigInt x in 2's complement.  (This never overflows its array).
// void leftShift_(x,n)         //left shift bigInt x by n bits.  n<bpe.
// void linComb_(x,y,a,b)       //do x=a*x+b*y for bigInts x and y and integers a and b
// void linCombShift_(x,y,b,ys) //do x=x+b*(y<<(ys*bpe)) for bigInts x and y, and integers b and ys
// void mont_(x,y,n,np)         //Montgomery multiplication (see comments where the function is defined)
// void multInt_(x,n)           //do x=x*n where x is a bigInt and n is an integer.
// void rightShift_(x,n)        //right shift bigInt x by n bits.  0 <= n < bpe. (This never overflows its array).
// void squareMod_(x,n)         //do x=x*x  mod n for bigInts x,n
// void subShift_(x,y,ys)       //do x=x-(y<<(ys*bpe)). Negative answers will be 2s complement.
//
// The following functions are based on algorithms from the _Handbook of Applied Cryptography_
//    powMod_()           = algorithm 14.94, Montgomery exponentiation
//    eGCD_,inverseMod_() = algorithm 14.61, Binary extended GCD_
//    GCD_()              = algorothm 14.57, Lehmer's algorithm
//    mont_()             = algorithm 14.36, Montgomery multiplication
//    divide_()           = algorithm 14.20  Multiple-precision division
//    squareMod_()        = algorithm 14.16  Multiple-precision squaring
//    randTruePrime_()    = algorithm  4.62, Maurer's algorithm
//    millerRabin()       = algorithm  4.24, Miller-Rabin algorithm
//
// Profiling shows:
//     randTruePrime_() spends:
//         10% of its time in calls to powMod_()
//         85% of its time in calls to millerRabin()
//     millerRabin() spends:
//         99% of its time in calls to powMod_()   (always with a base of 2)
//     powMod_() spends:
//         94% of its time in calls to mont_()  (almost always with x==y)
//
// This suggests there are several ways to speed up this library slightly:
//     - convert powMod_ to use a Montgomery form of k-ary window (or maybe a Montgomery form of sliding window)
//         -- this should especially focus on being fast when raising 2 to a power mod n
//     - convert randTruePrime_() to use a minimum r of 1/3 instead of 1/2 with the appropriate change to the test
//     - tune the parameters in randTruePrime_(), including c, m, and recLimit
//     - speed up the single loop in mont_() that takes 95% of the runtime, perhaps by reducing checking
//       within the loop when all the parameters are the same length.
//
// There are several ideas that look like they wouldn't help much at all:
//     - replacing trial division in randTruePrime_() with a sieve (that speeds up something taking almost no time anyway)
//     - increase bpe from 15 to 30 (that would help if we had a 32*32->64 multiplier, but not with JavaScript's 32*32->32)
//     - speeding up mont_(x,y,n,np) when x==y by doing a non-modular, non-Montgomery square
//       followed by a Montgomery reduction.  The intermediate answer will be twice as long as x, so that
//       method would be slower.  This is unfortunate because the code currently spends almost all of its time
//       doing mont_(x,x,...), both for randTruePrime_() and powMod_().  A faster method for Montgomery squaring
//       would have a large impact on the speed of randTruePrime_() and powMod_().  HAC has a couple of poorly-worded
//       sentences that seem to imply it's faster to do a non-modular square followed by a single
//       Montgomery reduction, but that's obviously wrong.
////////////////////////////////////////////////////////////////////////////////////////

//globals
bpe=0;         //bits stored per array element
mask=0;        //AND this with an array element to chop it down to bpe bits
radix=mask+1;  //equals 2^bpe.  A single 1 bit to the left of the last bit of mask.

//the digits for converting to different bases
digitsStr='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_=!@#$%^&*()[]{}|;:,.<>/?`~ \\\'\"+-';

//initialize the global variables
for (bpe=0; (1<<(bpe+1)) > (1<<bpe); bpe++);  //bpe=number of bits in the mantissa on this platform
bpe>>=1;                   //bpe=number of bits in one element of the array representing the bigInt
mask=(1<<bpe)-1;           //AND the mask with an integer to get its bpe least significant bits
radix=mask+1;              //2^bpe.  a single 1 bit to the left of the first bit of mask
one=int2bigInt(1,1,1);     //constant used in powMod_()

//the following global variables are scratchpad memory to 
//reduce dynamic memory allocation in the inner loop
t=new Array(0);
ss=t;       //used in mult_()
s0=t;       //used in multMod_(), squareMod_() 
s1=t;       //used in powMod_(), multMod_(), squareMod_() 
s2=t;       //used in powMod_(), multMod_()
s3=t;       //used in powMod_()
s4=t; s5=t; //used in mod_()
s6=t;       //used in bigInt2str()
s7=t;       //used in powMod_()
T=t;        //used in GCD_()
sa=t;       //used in mont_()
mr_x1=t; mr_r=t; mr_a=t;                                      //used in millerRabin()
eg_v=t; eg_u=t; eg_A=t; eg_B=t; eg_C=t; eg_D=t;               //used in eGCD_(), inverseMod_()
md_q1=t; md_q2=t; md_q3=t; md_r=t; md_r1=t; md_r2=t; md_tt=t; //used in mod_()

primes=t; pows=t; s_i=t; s_i2=t; s_R=t; s_rm=t; s_q=t; s_n1=t; 
  s_a=t; s_r2=t; s_n=t; s_b=t; s_d=t; s_x1=t; s_x2=t, s_aa=t; //used in randTruePrime_()
  
rpprb=t; //used in randProbPrimeRounds() (which also uses "primes")

////////////////////////////////////////////////////////////////////////////////////////


//return array of all primes less than integer n
function findPrimes(n) {
  var i,s,p,ans;
  s=new Array(n);
  for (i=0;i<n;i++)
    s[i]=0;
  s[0]=2;
  p=0;    //first p elements of s are primes, the rest are a sieve
  for(;s[p]<n;) {                  //s[p] is the pth prime
    for(i=s[p]*s[p]; i<n; i+=s[p]) //mark multiples of s[p]
      s[i]=1;
    p++;
    s[p]=s[p-1]+1;
    for(; s[p]<n && s[s[p]]; s[p]++); //find next prime (where s[p]==0)
  }
  ans=new Array(p);
  for(i=0;i<p;i++)
    ans[i]=s[i];
  return ans;
}


//does a single round of Miller-Rabin base b consider x to be a possible prime?
//x is a bigInt, and b is an integer, with b<x
function millerRabinInt(x,b) {
  if (mr_x1.length!=x.length) {
    mr_x1=dup(x);
    mr_r=dup(x);
    mr_a=dup(x);
  }

  copyInt_(mr_a,b);
  return millerRabin(x,mr_a);
}

//does a single round of Miller-Rabin base b consider x to be a possible prime?
//x and b are bigInts with b<x
function millerRabin(x,b) {
  var i,j,k,s;

  if (mr_x1.length!=x.length) {
    mr_x1=dup(x);
    mr_r=dup(x);
    mr_a=dup(x);
  }

  copy_(mr_a,b);
  copy_(mr_r,x);
  copy_(mr_x1,x);

  addInt_(mr_r,-1);
  addInt_(mr_x1,-1);

  //s=the highest power of two that divides mr_r
  k=0;
  for (i=0;i<mr_r.length;i++)
    for (j=1;j<mask;j<<=1)
      if (x[i] & j) {
        s=(k<mr_r.length+bpe ? k : 0); 
         i=mr_r.length;
         j=mask;
      } else
        k++;

  if (s)                
    rightShift_(mr_r,s);

  powMod_(mr_a,mr_r,x);

  if (!equalsInt(mr_a,1) && !equals(mr_a,mr_x1)) {
    j=1;
    while (j<=s-1 && !equals(mr_a,mr_x1)) {
      squareMod_(mr_a,x);
      if (equalsInt(mr_a,1)) {
        return 0;
      }
      j++;
    }
    if (!equals(mr_a,mr_x1)) {
      return 0;
    }
  }
  return 1;  
}

//returns how many bits long the bigInt is, not counting leading zeros.
function bitSize(x) {
  var j,z,w;
  for (j=x.length-1; (x[j]==0) && (j>0); j--);
  for (z=0,w=x[j]; w; (w>>=1),z++);
  z+=bpe*j;
  return z;
}

//return a copy of x with at least n elements, adding leading zeros if needed
function expand(x,n) {
  var ans=int2bigInt(0,(x.length>n ? x.length : n)*bpe,0);
  copy_(ans,x);
  return ans;
}

//return a k-bit true random prime using Maurer's algorithm.
function randTruePrime(k) {
  var ans=int2bigInt(0,k,0);
  randTruePrime_(ans,k);
  return trim(ans,1);
}

//return a k-bit random probable prime with probability of error < 2^-80
function randProbPrime(k) {
  if (k>=600) return randProbPrimeRounds(k,2); //numbers from HAC table 4.3
  if (k>=550) return randProbPrimeRounds(k,4);
  if (k>=500) return randProbPrimeRounds(k,5);
  if (k>=400) return randProbPrimeRounds(k,6);
  if (k>=350) return randProbPrimeRounds(k,7);
  if (k>=300) return randProbPrimeRounds(k,9);
  if (k>=250) return randProbPrimeRounds(k,12); //numbers from HAC table 4.4
  if (k>=200) return randProbPrimeRounds(k,15);
  if (k>=150) return randProbPrimeRounds(k,18);
  if (k>=100) return randProbPrimeRounds(k,27);
              return randProbPrimeRounds(k,40); //number from HAC remark 4.26 (only an estimate)
}

//return a k-bit probable random prime using n rounds of Miller Rabin (after trial division with small primes)	
function randProbPrimeRounds(k,n) {
  var ans, i, divisible, B; 
  B=30000;  //B is largest prime to use in trial division
  ans=int2bigInt(0,k,0);
  
  //optimization: try larger and smaller B to find the best limit.
  
  if (primes.length==0)
    primes=findPrimes(30000);  //check for divisibility by primes <=30000

  if (rpprb.length!=ans.length)
    rpprb=dup(ans);

  for (;;) { //keep trying random values for ans until one appears to be prime
    //optimization: pick a random number times L=2*3*5*...*p, plus a 
    //   random element of the list of all numbers in [0,L) not divisible by any prime up to p.
    //   This can reduce the amount of random number generation.
    
    randBigInt_(ans,k,0); //ans = a random odd number to check
    ans[0] |= 1; 
    divisible=0;
  
    //check ans for divisibility by small primes up to B
    for (i=0; (i<primes.length) && (primes[i]<=B); i++)
      if (modInt(ans,primes[i])==0 && !equalsInt(ans,primes[i])) {
        divisible=1;
        break;
      }      
    
    //optimization: change millerRabin so the base can be bigger than the number being checked, then eliminate the while here.
    
    //do n rounds of Miller Rabin, with random bases less than ans
    for (i=0; i<n && !divisible; i++) {
      randBigInt_(rpprb,k,0);
      while(!greater(ans,rpprb)) //pick a random rpprb that's < ans
        randBigInt_(rpprb,k,0);
      if (!millerRabin(ans,rpprb))
        divisible=1;
    }
    
    if(!divisible)
      return ans;
  }  
}

//return a new bigInt equal to (x mod n) for bigInts x and n.
function mod(x,n) {
  var ans=dup(x);
  mod_(ans,n);
  return trim(ans,1);
}

//return (x+n) where x is a bigInt and n is an integer.
function addInt(x,n) {
  var ans=expand(x,x.length+1);
  addInt_(ans,n);
  return trim(ans,1);
}

//return x*y for bigInts x and y. This is faster when y<x.
function mult(x,y) {
  var ans=expand(x,x.length+y.length);
  mult_(ans,y);
  return trim(ans,1);
}

//return (x**y mod n) where x,y,n are bigInts and ** is exponentiation.  0**0=1. Faster for odd n.
function powMod(x,y,n) {
  var ans=expand(x,n.length);  
  powMod_(ans,trim(y,2),trim(n,2),0);  //this should work without the trim, but doesn't
  return trim(ans,1);
}

//return (x-y) for bigInts x and y.  Negative answers will be 2s complement
function sub(x,y) {
  var ans=expand(x,(x.length>y.length ? x.length+1 : y.length+1)); 
  sub_(ans,y);
  return trim(ans,1);
}

//return (x+y) for bigInts x and y.  
function add(x,y) {
  var ans=expand(x,(x.length>y.length ? x.length+1 : y.length+1)); 
  add_(ans,y);
  return trim(ans,1);
}

//return (x**(-1) mod n) for bigInts x and n.  If no inverse exists, it returns null
function inverseMod(x,n) {
  var ans=expand(x,n.length); 
  var s;
  s=inverseMod_(ans,n);
  return s ? trim(ans,1) : null;
}

//return (x*y mod n) for bigInts x,y,n.  For greater speed, let y<x.
function multMod(x,y,n) {
  var ans=expand(x,n.length);
  multMod_(ans,y,n);
  return trim(ans,1);
}

//generate a k-bit true random prime using Maurer's algorithm,
//and put it into ans.  The bigInt ans must be large enough to hold it.
function randTruePrime_(ans,k) {
  var c,m,pm,dd,j,r,B,divisible,z,zz,recSize;

  if (primes.length==0)
    primes=findPrimes(30000);  //check for divisibility by primes <=30000

  if (pows.length==0) {
    pows=new Array(512);
    for (j=0;j<512;j++) {
      pows[j]=Math.pow(2,j/511.-1.);
    }
  }

  //c and m should be tuned for a particular machine and value of k, to maximize speed
  c=0.1;  //c=0.1 in HAC
  m=20;   //generate this k-bit number by first recursively generating a number that has between k/2 and k-m bits
  recLimit=20; //stop recursion when k <=recLimit.  Must have recLimit >= 2

  if (s_i2.length!=ans.length) {
    s_i2=dup(ans);
    s_R =dup(ans);
    s_n1=dup(ans);
    s_r2=dup(ans);
    s_d =dup(ans);
    s_x1=dup(ans);
    s_x2=dup(ans);
    s_b =dup(ans);
    s_n =dup(ans);
    s_i =dup(ans);
    s_rm=dup(ans);
    s_q =dup(ans);
    s_a =dup(ans);
    s_aa=dup(ans);
  }

  if (k <= recLimit) {  //generate small random primes by trial division up to its square root
    pm=(1<<((k+2)>>1))-1; //pm is binary number with all ones, just over sqrt(2^k)
    copyInt_(ans,0);
    for (dd=1;dd;) {
      dd=0;
      ans[0]= 1 | (1<<(k-1)) | Math.floor(Math.random()*(1<<k));  //random, k-bit, odd integer, with msb 1
      for (j=1;(j<primes.length) && ((primes[j]&pm)==primes[j]);j++) { //trial division by all primes 3...sqrt(2^k)
        if (0==(ans[0]%primes[j])) {
          dd=1;
          break;
        }
      }
    }
    carry_(ans);
    return;
  }

  B=c*k*k;    //try small primes up to B (or all the primes[] array if the largest is less than B).
  if (k>2*m)  //generate this k-bit number by first recursively generating a number that has between k/2 and k-m bits
    for (r=1; k-k*r<=m; )
      r=pows[Math.floor(Math.random()*512)];   //r=Math.pow(2,Math.random()-1);
  else
    r=.5;

  //simulation suggests the more complex algorithm using r=.333 is only slightly faster.

  recSize=Math.floor(r*k)+1;

  randTruePrime_(s_q,recSize);
  copyInt_(s_i2,0);
  s_i2[Math.floor((k-2)/bpe)] |= (1<<((k-2)%bpe));   //s_i2=2^(k-2)
  divide_(s_i2,s_q,s_i,s_rm);                        //s_i=floor((2^(k-1))/(2q))

  z=bitSize(s_i);

  for (;;) {
    for (;;) {  //generate z-bit numbers until one falls in the range [0,s_i-1]
      randBigInt_(s_R,z,0);
      if (greater(s_i,s_R))
        break;
    }                //now s_R is in the range [0,s_i-1]
    addInt_(s_R,1);  //now s_R is in the range [1,s_i]
    add_(s_R,s_i);   //now s_R is in the range [s_i+1,2*s_i]

    copy_(s_n,s_q);
    mult_(s_n,s_R); 
    multInt_(s_n,2);
    addInt_(s_n,1);    //s_n=2*s_R*s_q+1
    
    copy_(s_r2,s_R);
    multInt_(s_r2,2);  //s_r2=2*s_R

    //check s_n for divisibility by small primes up to B
    for (divisible=0,j=0; (j<primes.length) && (primes[j]<B); j++)
      if (modInt(s_n,primes[j])==0 && !equalsInt(s_n,primes[j])) {
        divisible=1;
        break;
      }      

    if (!divisible)    //if it passes small primes check, then try a single Miller-Rabin base 2
      if (!millerRabinInt(s_n,2)) //this line represents 75% of the total runtime for randTruePrime_ 
        divisible=1;

    if (!divisible) {  //if it passes that test, continue checking s_n
      addInt_(s_n,-3);
      for (j=s_n.length-1;(s_n[j]==0) && (j>0); j--);  //strip leading zeros
      for (zz=0,w=s_n[j]; w; (w>>=1),zz++);
      zz+=bpe*j;                             //zz=number of bits in s_n, ignoring leading zeros
      for (;;) {  //generate z-bit numbers until one falls in the range [0,s_n-1]
        randBigInt_(s_a,zz,0);
        if (greater(s_n,s_a))
          break;
      }                //now s_a is in the range [0,s_n-1]
      addInt_(s_n,3);  //now s_a is in the range [0,s_n-4]
      addInt_(s_a,2);  //now s_a is in the range [2,s_n-2]
      copy_(s_b,s_a);
      copy_(s_n1,s_n);
      addInt_(s_n1,-1);
      powMod_(s_b,s_n1,s_n);   //s_b=s_a^(s_n-1) modulo s_n
      addInt_(s_b,-1);
      if (isZero(s_b)) {
        copy_(s_b,s_a);
        powMod_(s_b,s_r2,s_n);
        addInt_(s_b,-1);
        copy_(s_aa,s_n);
        copy_(s_d,s_b);
        GCD_(s_d,s_n);  //if s_b and s_n are relatively prime, then s_n is a prime
        if (equalsInt(s_d,1)) {
          copy_(ans,s_aa);
          return;     //if we've made it this far, then s_n is absolutely guaranteed to be prime
        }
      }
    }
  }
}

//Return an n-bit random BigInt (n>=1).  If s=1, then the most significant of those n bits is set to 1.
function randBigInt(n,s) {
  var a,b;
  a=Math.floor((n-1)/bpe)+2; //# array elements to hold the BigInt with a leading 0 element
  b=int2bigInt(0,0,a);
  randBigInt_(b,n,s);
  return b;
}

//Set b to an n-bit random BigInt.  If s=1, then the most significant of those n bits is set to 1.
//Array b must be big enough to hold the result. Must have n>=1
function randBigInt_(b,n,s) {
  var i,a;
  for (i=0;i<b.length;i++)
    b[i]=0;
  a=Math.floor((n-1)/bpe)+1; //# array elements to hold the BigInt
  for (i=0;i<a;i++) {
    b[i]=Math.floor(Math.random()*(1<<(bpe-1)));
  }
  b[a-1] &= (2<<((n-1)%bpe))-1;
  if (s==1)
    b[a-1] |= (1<<((n-1)%bpe));
}

//Return the greatest common divisor of bigInts x and y (each with same number of elements).
function GCD(x,y) {
  var xc,yc;
  xc=dup(x);
  yc=dup(y);
  GCD_(xc,yc);
  return xc;
}

//set x to the greatest common divisor of bigInts x and y (each with same number of elements).
//y is destroyed.
function GCD_(x,y) {
  var i,xp,yp,A,B,C,D,q,sing;
  if (T.length!=x.length)
    T=dup(x);

  sing=1;
  while (sing) { //while y has nonzero elements other than y[0]
    sing=0;
    for (i=1;i<y.length;i++) //check if y has nonzero elements other than 0
      if (y[i]) {
        sing=1;
        break;
      }
    if (!sing) break; //quit when y all zero elements except possibly y[0]

    for (i=x.length;!x[i] && i>=0;i--);  //find most significant element of x
    xp=x[i];
    yp=y[i];
    A=1; B=0; C=0; D=1;
    while ((yp+C) && (yp+D)) {
      q =Math.floor((xp+A)/(yp+C));
      qp=Math.floor((xp+B)/(yp+D));
      if (q!=qp)
        break;
      t= A-q*C;   A=C;   C=t;    //  do (A,B,xp, C,D,yp) = (C,D,yp, A,B,xp) - q*(0,0,0, C,D,yp)      
      t= B-q*D;   B=D;   D=t;
      t=xp-q*yp; xp=yp; yp=t;
    }
    if (B) {
      copy_(T,x);
      linComb_(x,y,A,B); //x=A*x+B*y
      linComb_(y,T,D,C); //y=D*y+C*T
    } else {
      mod_(x,y);
      copy_(T,x);
      copy_(x,y);
      copy_(y,T);
    } 
  }
  if (y[0]==0)
    return;
  t=modInt(x,y[0]);
  copyInt_(x,y[0]);
  y[0]=t;
  while (y[0]) {
    x[0]%=y[0];
    t=x[0]; x[0]=y[0]; y[0]=t;
  }
}

//do x=x**(-1) mod n, for bigInts x and n.
//If no inverse exists, it sets x to zero and returns 0, else it returns 1.
//The x array must be at least as large as the n array.
function inverseMod_(x,n) {
  var k=1+2*Math.max(x.length,n.length);

  if(!(x[0]&1)  && !(n[0]&1)) {  //if both inputs are even, then inverse doesn't exist
    copyInt_(x,0);
    return 0;
  }

  if (eg_u.length!=k) {
    eg_u=new Array(k);
    eg_v=new Array(k);
    eg_A=new Array(k);
    eg_B=new Array(k);
    eg_C=new Array(k);
    eg_D=new Array(k);
  }

  copy_(eg_u,x);
  copy_(eg_v,n);
  copyInt_(eg_A,1);
  copyInt_(eg_B,0);
  copyInt_(eg_C,0);
  copyInt_(eg_D,1);
  for (;;) {
    while(!(eg_u[0]&1)) {  //while eg_u is even
      halve_(eg_u);
      if (!(eg_A[0]&1) && !(eg_B[0]&1)) { //if eg_A==eg_B==0 mod 2
        halve_(eg_A);
        halve_(eg_B);      
      } else {
        add_(eg_A,n);  halve_(eg_A);
        sub_(eg_B,x);  halve_(eg_B);
      }
    }

    while (!(eg_v[0]&1)) {  //while eg_v is even
      halve_(eg_v);
      if (!(eg_C[0]&1) && !(eg_D[0]&1)) { //if eg_C==eg_D==0 mod 2
        halve_(eg_C);
        halve_(eg_D);      
      } else {
        add_(eg_C,n);  halve_(eg_C);
        sub_(eg_D,x);  halve_(eg_D);
      }
    }

    if (!greater(eg_v,eg_u)) { //eg_v <= eg_u
      sub_(eg_u,eg_v);
      sub_(eg_A,eg_C);
      sub_(eg_B,eg_D);
    } else {                   //eg_v > eg_u
      sub_(eg_v,eg_u);
      sub_(eg_C,eg_A);
      sub_(eg_D,eg_B);
    }
  
    if (equalsInt(eg_u,0)) {
      if (negative(eg_C)) //make sure answer is nonnegative
        add_(eg_C,n);
      copy_(x,eg_C);

      if (!equalsInt(eg_v,1)) { //if GCD_(x,n)!=1, then there is no inverse
        copyInt_(x,0);
        return 0;
      }
      return 1;
    }
  }
}

//return x**(-1) mod n, for integers x and n.  Return 0 if there is no inverse
function inverseModInt(x,n) {
  var a=1,b=0,t;
  for (;;) {
    if (x==1) return a;
    if (x==0) return 0;
    b-=a*Math.floor(n/x);
    n%=x;

    if (n==1) return b; //to avoid negatives, change this b to n-b, and each -= to +=
    if (n==0) return 0;
    a-=b*Math.floor(x/n);
    x%=n;
  }
}

//this deprecated function is for backward compatibility only. 
function inverseModInt_(x,n) {
   return inverseModInt(x,n);
}


//Given positive bigInts x and y, change the bigints v, a, and b to positive bigInts such that:
//     v = GCD_(x,y) = a*x-b*y
//The bigInts v, a, b, must have exactly as many elements as the larger of x and y.
function eGCD_(x,y,v,a,b) {
  var g=0;
  var k=Math.max(x.length,y.length);
  if (eg_u.length!=k) {
    eg_u=new Array(k);
    eg_A=new Array(k);
    eg_B=new Array(k);
    eg_C=new Array(k);
    eg_D=new Array(k);
  }
  while(!(x[0]&1)  && !(y[0]&1)) {  //while x and y both even
    halve_(x);
    halve_(y);
    g++;
  }
  copy_(eg_u,x);
  copy_(v,y);
  copyInt_(eg_A,1);
  copyInt_(eg_B,0);
  copyInt_(eg_C,0);
  copyInt_(eg_D,1);
  for (;;) {
    while(!(eg_u[0]&1)) {  //while u is even
      halve_(eg_u);
      if (!(eg_A[0]&1) && !(eg_B[0]&1)) { //if A==B==0 mod 2
        halve_(eg_A);
        halve_(eg_B);      
      } else {
        add_(eg_A,y);  halve_(eg_A);
        sub_(eg_B,x);  halve_(eg_B);
      }
    }

    while (!(v[0]&1)) {  //while v is even
      halve_(v);
      if (!(eg_C[0]&1) && !(eg_D[0]&1)) { //if C==D==0 mod 2
        halve_(eg_C);
        halve_(eg_D);      
      } else {
        add_(eg_C,y);  halve_(eg_C);
        sub_(eg_D,x);  halve_(eg_D);
      }
    }

    if (!greater(v,eg_u)) { //v<=u
      sub_(eg_u,v);
      sub_(eg_A,eg_C);
      sub_(eg_B,eg_D);
    } else {                //v>u
      sub_(v,eg_u);
      sub_(eg_C,eg_A);
      sub_(eg_D,eg_B);
    }
    if (equalsInt(eg_u,0)) {
      if (negative(eg_C)) {   //make sure a (C)is nonnegative
        add_(eg_C,y);
        sub_(eg_D,x);
      }
      multInt_(eg_D,-1);  ///make sure b (D) is nonnegative
      copy_(a,eg_C);
      copy_(b,eg_D);
      leftShift_(v,g);
      return;
    }
  }
}


//is bigInt x negative?
function negative(x) {
  return ((x[x.length-1]>>(bpe-1))&1);
}


//is (x << (shift*bpe)) > y?
//x and y are nonnegative bigInts
//shift is a nonnegative integer
function greaterShift(x,y,shift) {
  var i, kx=x.length, ky=y.length;
  k=((kx+shift)<ky) ? (kx+shift) : ky;
  for (i=ky-1-shift; i<kx && i>=0; i++) 
    if (x[i]>0)
      return 1; //if there are nonzeros in x to the left of the first column of y, then x is bigger
  for (i=kx-1+shift; i<ky; i++)
    if (y[i]>0)
      return 0; //if there are nonzeros in y to the left of the first column of x, then x is not bigger
  for (i=k-1; i>=shift; i--)
    if      (x[i-shift]>y[i]) return 1;
    else if (x[i-shift]<y[i]) return 0;
  return 0;
}

//is x > y? (x and y both nonnegative)
function greater(x,y) {
  var i;
  var k=(x.length<y.length) ? x.length : y.length;

  for (i=x.length;i<y.length;i++)
    if (y[i])
      return 0;  //y has more digits

  for (i=y.length;i<x.length;i++)
    if (x[i])
      return 1;  //x has more digits

  for (i=k-1;i>=0;i--)
    if (x[i]>y[i])
      return 1;
    else if (x[i]<y[i])
      return 0;
  return 0;
}

//divide x by y giving quotient q and remainder r.  (q=floor(x/y),  r=x mod y).  All 4 are bigints.
//x must have at least one leading zero element.
//y must be nonzero.
//q and r must be arrays that are exactly the same length as x. (Or q can have more).
//Must have x.length >= y.length >= 2.
function divide_(x,y,q,r) {
  var kx, ky;
  var i,j,y1,y2,c,a,b;
  copy_(r,x);
  for (ky=y.length;y[ky-1]==0;ky--); //ky is number of elements in y, not including leading zeros

  //normalize: ensure the most significant element of y has its highest bit set  
  b=y[ky-1];
  for (a=0; b; a++)
    b>>=1;  
  a=bpe-a;  //a is how many bits to shift so that the high order bit of y is leftmost in its array element
  leftShift_(y,a);  //multiply both by 1<<a now, then divide both by that at the end
  leftShift_(r,a);

  //Rob Visser discovered a bug: the following line was originally just before the normalization.
  for (kx=r.length;r[kx-1]==0 && kx>ky;kx--); //kx is number of elements in normalized x, not including leading zeros

  copyInt_(q,0);                      // q=0
  while (!greaterShift(y,r,kx-ky)) {  // while (leftShift_(y,kx-ky) <= r) {
    subShift_(r,y,kx-ky);             //   r=r-leftShift_(y,kx-ky)
    q[kx-ky]++;                       //   q[kx-ky]++;
  }                                   // }

  for (i=kx-1; i>=ky; i--) {
    if (r[i]==y[ky-1])
      q[i-ky]=mask;
    else
      q[i-ky]=Math.floor((r[i]*radix+r[i-1])/y[ky-1]);	

    //The following for(;;) loop is equivalent to the commented while loop, 
    //except that the uncommented version avoids overflow.
    //The commented loop comes from HAC, which assumes r[-1]==y[-1]==0
    //  while (q[i-ky]*(y[ky-1]*radix+y[ky-2]) > r[i]*radix*radix+r[i-1]*radix+r[i-2])
    //    q[i-ky]--;    
    for (;;) {
      y2=(ky>1 ? y[ky-2] : 0)*q[i-ky];
      c=y2>>bpe;
      y2=y2 & mask;
      y1=c+q[i-ky]*y[ky-1];
      c=y1>>bpe;
      y1=y1 & mask;

      if (c==r[i] ? y1==r[i-1] ? y2>(i>1 ? r[i-2] : 0) : y1>r[i-1] : c>r[i]) 
        q[i-ky]--;
      else
        break;
    }

    linCombShift_(r,y,-q[i-ky],i-ky);    //r=r-q[i-ky]*leftShift_(y,i-ky)
    if (negative(r)) {
      addShift_(r,y,i-ky);         //r=r+leftShift_(y,i-ky)
      q[i-ky]--;
    }
  }

  rightShift_(y,a);  //undo the normalization step
  rightShift_(r,a);  //undo the normalization step
}

//do carries and borrows so each element of the bigInt x fits in bpe bits.
function carry_(x) {
  var i,k,c,b;
  k=x.length;
  c=0;
  for (i=0;i<k;i++) {
    c+=x[i];
    b=0;
    if (c<0) {
      b=-(c>>bpe);
      c+=b*radix;
    }
    x[i]=c & mask;
    c=(c>>bpe)-b;
  }
}

//return x mod n for bigInt x and integer n.
function modInt(x,n) {
  var i,c=0;
  for (i=x.length-1; i>=0; i--)
    c=(c*radix+x[i])%n;
  return c;
}

//convert the integer t into a bigInt with at least the given number of bits.
//the returned array stores the bigInt in bpe-bit chunks, little endian (buff[0] is least significant word)
//Pad the array with leading zeros so that it has at least minSize elements.
//There will always be at least one leading 0 element.
function int2bigInt(t,bits,minSize) {   
  var i,k;
  k=Math.ceil(bits/bpe)+1;
  k=minSize>k ? minSize : k;
  buff=new Array(k);
  copyInt_(buff,t);
  return buff;
}

//return the bigInt given a string representation in a given base.  
//Pad the array with leading zeros so that it has at least minSize elements.
//If base=-1, then it reads in a space-separated list of array elements in decimal.
//The array will always have at least one leading zero, unless base=-1.
function str2bigInt(s,base,minSize) {
  var d, i, j, x, y, kk;
  var k=s.length;
  if (base==-1) { //comma-separated list of array elements in decimal
    x=new Array(0);
    for (;;) {
      y=new Array(x.length+1);
      for (i=0;i<x.length;i++)
        y[i+1]=x[i];
      y[0]=parseInt(s,10);
      x=y;
      d=s.indexOf(',',0);
      if (d<1) 
        break;
      s=s.substring(d+1);
      if (s.length==0)
        break;
    }
    if (x.length<minSize) {
      y=new Array(minSize);
      copy_(y,x);
      return y;
    }
    return x;
  }

  x=int2bigInt(0,base*k,0);
  for (i=0;i<k;i++) {
    d=digitsStr.indexOf(s.substring(i,i+1),0);
    if (base<=36 && d>=36)  //convert lowercase to uppercase if base<=36
      d-=26;
    if (d>=base || d<0) {   //stop at first illegal character
      break;
    }
    multInt_(x,base);
    addInt_(x,d);
  }

  for (k=x.length;k>0 && !x[k-1];k--); //strip off leading zeros
  k=minSize>k+1 ? minSize : k+1;
  y=new Array(k);
  kk=k<x.length ? k : x.length;
  for (i=0;i<kk;i++)
    y[i]=x[i];
  for (;i<k;i++)
    y[i]=0;
  return y;
}

//is bigint x equal to integer y?
//y must have less than bpe bits
function equalsInt(x,y) {
  var i;
  if (x[0]!=y)
    return 0;
  for (i=1;i<x.length;i++)
    if (x[i])
      return 0;
  return 1;
}

//are bigints x and y equal?
//this works even if x and y are different lengths and have arbitrarily many leading zeros
function equals(x,y) {
  var i;
  var k=x.length<y.length ? x.length : y.length;
  for (i=0;i<k;i++)
    if (x[i]!=y[i])
      return 0;
  if (x.length>y.length) {
    for (;i<x.length;i++)
      if (x[i])
        return 0;
  } else {
    for (;i<y.length;i++)
      if (y[i])
        return 0;
  }
  return 1;
}

//is the bigInt x equal to zero?
function isZero(x) {
  var i;
  for (i=0;i<x.length;i++)
    if (x[i])
      return 0;
  return 1;
}

//convert a bigInt into a string in a given base, from base 2 up to base 95.
//Base -1 prints the contents of the array representing the number.
function bigInt2str(x,base) {
  var i,t,s="";

  if (s6.length!=x.length) 
    s6=dup(x);
  else
    copy_(s6,x);

  if (base==-1) { //return the list of array contents
    for (i=x.length-1;i>0;i--)
      s+=x[i]+',';
    s+=x[0];
  }
  else { //return it in the given base
    while (!isZero(s6)) {
      t=divInt_(s6,base);  //t=s6 % base; s6=floor(s6/base);
      s=digitsStr.substring(t,t+1)+s;
    }
  }
  if (s.length==0)
    s="0";
  return s;
}

//returns a duplicate of bigInt x
function dup(x) {
  var i;
  buff=new Array(x.length);
  copy_(buff,x);
  return buff;
}

//do x=y on bigInts x and y.  x must be an array at least as big as y (not counting the leading zeros in y).
function copy_(x,y) {
  var i;
  var k=x.length<y.length ? x.length : y.length;
  for (i=0;i<k;i++)
    x[i]=y[i];
  for (i=k;i<x.length;i++)
    x[i]=0;
}

//do x=y on bigInt x and integer y.  
function copyInt_(x,n) {
  var i,c;
  for (c=n,i=0;i<x.length;i++) {
    x[i]=c & mask;
    c>>=bpe;
  }
}

//do x=x+n where x is a bigInt and n is an integer.
//x must be large enough to hold the result.
function addInt_(x,n) {
  var i,k,c,b;
  x[0]+=n;
  k=x.length;
  c=0;
  for (i=0;i<k;i++) {
    c+=x[i];
    b=0;
    if (c<0) {
      b=-(c>>bpe);
      c+=b*radix;
    }
    x[i]=c & mask;
    c=(c>>bpe)-b;
    if (!c) return; //stop carrying as soon as the carry is zero
  }
}

//right shift bigInt x by n bits.  0 <= n < bpe.
function rightShift_(x,n) {
  var i;
  var k=Math.floor(n/bpe);
  if (k) {
    for (i=0;i<x.length-k;i++) //right shift x by k elements
      x[i]=x[i+k];
    for (;i<x.length;i++)
      x[i]=0;
    n%=bpe;
  }
  for (i=0;i<x.length-1;i++) {
    x[i]=mask & ((x[i+1]<<(bpe-n)) | (x[i]>>n));
  }
  x[i]>>=n;
}

//do x=floor(|x|/2)*sgn(x) for bigInt x in 2's complement
function halve_(x) {
  var i;
  for (i=0;i<x.length-1;i++) {
    x[i]=mask & ((x[i+1]<<(bpe-1)) | (x[i]>>1));
  }
  x[i]=(x[i]>>1) | (x[i] & (radix>>1));  //most significant bit stays the same
}

//left shift bigInt x by n bits.
function leftShift_(x,n) {
  var i;
  var k=Math.floor(n/bpe);
  if (k) {
    for (i=x.length; i>=k; i--) //left shift x by k elements
      x[i]=x[i-k];
    for (;i>=0;i--)
      x[i]=0;  
    n%=bpe;
  }
  if (!n)
    return;
  for (i=x.length-1;i>0;i--) {
    x[i]=mask & ((x[i]<<n) | (x[i-1]>>(bpe-n)));
  }
  x[i]=mask & (x[i]<<n);
}

//do x=x*n where x is a bigInt and n is an integer.
//x must be large enough to hold the result.
function multInt_(x,n) {
  var i,k,c,b;
  if (!n)
    return;
  k=x.length;
  c=0;
  for (i=0;i<k;i++) {
    c+=x[i]*n;
    b=0;
    if (c<0) {
      b=-(c>>bpe);
      c+=b*radix;
    }
    x[i]=c & mask;
    c=(c>>bpe)-b;
  }
}

//do x=floor(x/n) for bigInt x and integer n, and return the remainder
function divInt_(x,n) {
  var i,r=0,s;
  for (i=x.length-1;i>=0;i--) {
    s=r*radix+x[i];
    x[i]=Math.floor(s/n);
    r=s%n;
  }
  return r;
}

//do the linear combination x=a*x+b*y for bigInts x and y, and integers a and b.
//x must be large enough to hold the answer.
function linComb_(x,y,a,b) {
  var i,c,k,kk;
  k=x.length<y.length ? x.length : y.length;
  kk=x.length;
  for (c=0,i=0;i<k;i++) {
    c+=a*x[i]+b*y[i];
    x[i]=c & mask;
    c>>=bpe;
  }
  for (i=k;i<kk;i++) {
    c+=a*x[i];
    x[i]=c & mask;
    c>>=bpe;
  }
}

//do the linear combination x=a*x+b*(y<<(ys*bpe)) for bigInts x and y, and integers a, b and ys.
//x must be large enough to hold the answer.
function linCombShift_(x,y,b,ys) {
  var i,c,k,kk;
  k=x.length<ys+y.length ? x.length : ys+y.length;
  kk=x.length;
  for (c=0,i=ys;i<k;i++) {
    c+=x[i]+b*y[i-ys];
    x[i]=c & mask;
    c>>=bpe;
  }
  for (i=k;c && i<kk;i++) {
    c+=x[i];
    x[i]=c & mask;
    c>>=bpe;
  }
}

//do x=x+(y<<(ys*bpe)) for bigInts x and y, and integers a,b and ys.
//x must be large enough to hold the answer.
function addShift_(x,y,ys) {
  var i,c,k,kk;
  k=x.length<ys+y.length ? x.length : ys+y.length;
  kk=x.length;
  for (c=0,i=ys;i<k;i++) {
    c+=x[i]+y[i-ys];
    x[i]=c & mask;
    c>>=bpe;
  }
  for (i=k;c && i<kk;i++) {
    c+=x[i];
    x[i]=c & mask;
    c>>=bpe;
  }
}

//do x=x-(y<<(ys*bpe)) for bigInts x and y, and integers a,b and ys.
//x must be large enough to hold the answer.
function subShift_(x,y,ys) {
  var i,c,k,kk;
  k=x.length<ys+y.length ? x.length : ys+y.length;
  kk=x.length;
  for (c=0,i=ys;i<k;i++) {
    c+=x[i]-y[i-ys];
    x[i]=c & mask;
    c>>=bpe;
  }
  for (i=k;c && i<kk;i++) {
    c+=x[i];
    x[i]=c & mask;
    c>>=bpe;
  }
}

//do x=x-y for bigInts x and y.
//x must be large enough to hold the answer.
//negative answers will be 2s complement
function sub_(x,y) {
  var i,c,k,kk;
  k=x.length<y.length ? x.length : y.length;
  for (c=0,i=0;i<k;i++) {
    c+=x[i]-y[i];
    x[i]=c & mask;
    c>>=bpe;
  }
  for (i=k;c && i<x.length;i++) {
    c+=x[i];
    x[i]=c & mask;
    c>>=bpe;
  }
}

//do x=x+y for bigInts x and y.
//x must be large enough to hold the answer.
function add_(x,y) {
  var i,c,k,kk;
  k=x.length<y.length ? x.length : y.length;
  for (c=0,i=0;i<k;i++) {
    c+=x[i]+y[i];
    x[i]=c & mask;
    c>>=bpe;
  }
  for (i=k;c && i<x.length;i++) {
    c+=x[i];
    x[i]=c & mask;
    c>>=bpe;
  }
}

//do x=x*y for bigInts x and y.  This is faster when y<x.
function mult_(x,y) {
  var i;
  if (ss.length!=2*x.length)
    ss=new Array(2*x.length);
  copyInt_(ss,0);
  for (i=0;i<y.length;i++)
    if (y[i])
      linCombShift_(ss,x,y[i],i);   //ss=1*ss+y[i]*(x<<(i*bpe))
  copy_(x,ss);
}

//do x=x mod n for bigInts x and n.
function mod_(x,n) {
  if (s4.length!=x.length)
    s4=dup(x);
  else
    copy_(s4,x);
  if (s5.length!=x.length)
    s5=dup(x);  
  divide_(s4,n,s5,x);  //x = remainder of s4 / n
}

//do x=x*y mod n for bigInts x,y,n.
//for greater speed, let y<x.
function multMod_(x,y,n) {
  var i;
  if (s0.length!=2*x.length)
    s0=new Array(2*x.length);
  copyInt_(s0,0);
  for (i=0;i<y.length;i++)
    if (y[i])
      linCombShift_(s0,x,y[i],i);   //s0=1*s0+y[i]*(x<<(i*bpe))
  mod_(s0,n);
  copy_(x,s0);
}

//do x=x*x mod n for bigInts x,n.
function squareMod_(x,n) {
  var i,j,d,c,kx,kn,k;
  for (kx=x.length; kx>0 && !x[kx-1]; kx--);  //ignore leading zeros in x
  k=kx>n.length ? 2*kx : 2*n.length; //k=# elements in the product, which is twice the elements in the larger of x and n
  if (s0.length!=k) 
    s0=new Array(k);
  copyInt_(s0,0);
  for (i=0;i<kx;i++) {
    c=s0[2*i]+x[i]*x[i];
    s0[2*i]=c & mask;
    c>>=bpe;
    for (j=i+1;j<kx;j++) {
      c=s0[i+j]+2*x[i]*x[j]+c;
      s0[i+j]=(c & mask);
      c>>=bpe;
    }
    s0[i+kx]=c;
  }
  mod_(s0,n);
  copy_(x,s0);
}

//return x with exactly k leading zero elements
function trim(x,k) {
  var i,y;
  for (i=x.length; i>0 && !x[i-1]; i--);
  y=new Array(i+k);
  copy_(y,x);
  return y;
}

//do x=x**y mod n, where x,y,n are bigInts and ** is exponentiation.  0**0=1.
//this is faster when n is odd.  x usually needs to have as many elements as n.
function powMod_(x,y,n) {
  var k1,k2,kn,np;
  if(s7.length!=n.length)
    s7=dup(n);

  //for even modulus, use a simple square-and-multiply algorithm,
  //rather than using the more complex Montgomery algorithm.
  if ((n[0]&1)==0) {
    copy_(s7,x);
    copyInt_(x,1);
    while(!equalsInt(y,0)) {
      if (y[0]&1)
        multMod_(x,s7,n);
      divInt_(y,2);
      squareMod_(s7,n); 
    }
    return;
  }

  //calculate np from n for the Montgomery multiplications
  copyInt_(s7,0);
  for (kn=n.length;kn>0 && !n[kn-1];kn--);
  np=radix-inverseModInt(modInt(n,radix),radix);
  s7[kn]=1;
  multMod_(x ,s7,n);   // x = x * 2**(kn*bp) mod n

  if (s3.length!=x.length)
    s3=dup(x);
  else
    copy_(s3,x);

  for (k1=y.length-1;k1>0 & !y[k1]; k1--);  //k1=first nonzero element of y
  if (y[k1]==0) {  //anything to the 0th power is 1
    copyInt_(x,1);
    return;
  }
  for (k2=1<<(bpe-1);k2 && !(y[k1] & k2); k2>>=1);  //k2=position of first 1 bit in y[k1]
  for (;;) {
    if (!(k2>>=1)) {  //look at next bit of y
      k1--;
      if (k1<0) {
        mont_(x,one,n,np);
        return;
      }
      k2=1<<(bpe-1);
    }    
    mont_(x,x,n,np);

    if (k2 & y[k1]) //if next bit is a 1
      mont_(x,s3,n,np);
  }
}


//do x=x*y*Ri mod n for bigInts x,y,n, 
//  where Ri = 2**(-kn*bpe) mod n, and kn is the 
//  number of elements in the n array, not 
//  counting leading zeros.  
//x array must have at least as many elemnts as the n array
//It's OK if x and y are the same variable.
//must have:
//  x,y < n
//  n is odd
//  np = -(n^(-1)) mod radix
function mont_(x,y,n,np) {
  var i,j,c,ui,t,ks;
  var kn=n.length;
  var ky=y.length;

  if (sa.length!=kn)
    sa=new Array(kn);
    
  copyInt_(sa,0);

  for (;kn>0 && n[kn-1]==0;kn--); //ignore leading zeros of n
  for (;ky>0 && y[ky-1]==0;ky--); //ignore leading zeros of y
  ks=sa.length-1; //sa will never have more than this many nonzero elements.  

  //the following loop consumes 95% of the runtime for randTruePrime_() and powMod_() for large numbers
  for (i=0; i<kn; i++) {
    t=sa[0]+x[i]*y[0];
    ui=((t & mask) * np) & mask;  //the inner "& mask" was needed on Safari (but not MSIE) at one time
    c=(t+ui*n[0]) >> bpe;
    t=x[i];
    
    //do sa=(sa+x[i]*y+ui*n)/b   where b=2**bpe.  Loop is unrolled 5-fold for speed
    j=1;
    for (;j<ky-4;) { c+=sa[j]+ui*n[j]+t*y[j];   sa[j-1]=c & mask;   c>>=bpe;   j++;
                     c+=sa[j]+ui*n[j]+t*y[j];   sa[j-1]=c & mask;   c>>=bpe;   j++;
                     c+=sa[j]+ui*n[j]+t*y[j];   sa[j-1]=c & mask;   c>>=bpe;   j++;
                     c+=sa[j]+ui*n[j]+t*y[j];   sa[j-1]=c & mask;   c>>=bpe;   j++;
                     c+=sa[j]+ui*n[j]+t*y[j];   sa[j-1]=c & mask;   c>>=bpe;   j++; }    
    for (;j<ky;)   { c+=sa[j]+ui*n[j]+t*y[j];   sa[j-1]=c & mask;   c>>=bpe;   j++; }
    for (;j<kn-4;) { c+=sa[j]+ui*n[j];          sa[j-1]=c & mask;   c>>=bpe;   j++;
                     c+=sa[j]+ui*n[j];          sa[j-1]=c & mask;   c>>=bpe;   j++;
                     c+=sa[j]+ui*n[j];          sa[j-1]=c & mask;   c>>=bpe;   j++;
                     c+=sa[j]+ui*n[j];          sa[j-1]=c & mask;   c>>=bpe;   j++;
                     c+=sa[j]+ui*n[j];          sa[j-1]=c & mask;   c>>=bpe;   j++; }  
    for (;j<kn;)   { c+=sa[j]+ui*n[j];          sa[j-1]=c & mask;   c>>=bpe;   j++; }   
    for (;j<ks;)   { c+=sa[j];                  sa[j-1]=c & mask;   c>>=bpe;   j++; }  
    sa[j-1]=c & mask;
  }

  if (!greater(n,sa))
    sub_(sa,n);
  copy_(x,sa);
}

//Base64 encoding and decoding
var Base64 = {
// private property
_keyStr : "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/=",

// public method for encoding
encode : function (input) {
    var output = "";
    var chr1, chr2, chr3, enc1, enc2, enc3, enc4;
    var i = 0;

    input = Base64._utf8_encode(input);

    while (i < input.length) {

        chr1 = input.charCodeAt(i++);
        chr2 = input.charCodeAt(i++);
        chr3 = input.charCodeAt(i++);

        enc1 = chr1 >> 2;
        enc2 = ((chr1 & 3) << 4) | (chr2 >> 4);
        enc3 = ((chr2 & 15) << 2) | (chr3 >> 6);
        enc4 = chr3 & 63;

        if (isNaN(chr2)) {
            enc3 = enc4 = 64;
        } else if (isNaN(chr3)) {
            enc4 = 64;
        }

        output = output +
        Base64._keyStr.charAt(enc1) + Base64._keyStr.charAt(enc2) +
        Base64._keyStr.charAt(enc3) + Base64._keyStr.charAt(enc4);

    }

    return output;
},

// public method for decoding
decode : function (input) {
    var output = "";
    var chr1, chr2, chr3;
    var enc1, enc2, enc3, enc4;
    var i = 0;

    input = input.replace(/[^A-Za-z0-9\+\/\=]/g, "");

    while (i < input.length) {

        enc1 = Base64._keyStr.indexOf(input.charAt(i++));
        enc2 = Base64._keyStr.indexOf(input.charAt(i++));
        enc3 = Base64._keyStr.indexOf(input.charAt(i++));
        enc4 = Base64._keyStr.indexOf(input.charAt(i++));

        chr1 = (enc1 << 2) | (enc2 >> 4);
        chr2 = ((enc2 & 15) << 4) | (enc3 >> 2);
        chr3 = ((enc3 & 3) << 6) | enc4;

        output = output + String.fromCharCode(chr1);

        if (enc3 != 64) {
            output = output + String.fromCharCode(chr2);
        }
        if (enc4 != 64) {
            output = output + String.fromCharCode(chr3);
        }

    }

    output = Base64._utf8_decode(output);

    return output;

},

// private method for UTF-8 encoding
_utf8_encode : function (string) {
    string = string.replace(/\r\n/g,"\n");
    var utftext = "";

    for (var n = 0; n < string.length; n++) {

        var c = string.charCodeAt(n);

        if (c < 128) {
            utftext += String.fromCharCode(c);
        }
        else if((c > 127) && (c < 2048)) {
            utftext += String.fromCharCode((c >> 6) | 192);
            utftext += String.fromCharCode((c & 63) | 128);
        }
        else {
            utftext += String.fromCharCode((c >> 12) | 224);
            utftext += String.fromCharCode(((c >> 6) & 63) | 128);
            utftext += String.fromCharCode((c & 63) | 128);
        }

    }

    return utftext;
},

// private method for UTF-8 decoding
_utf8_decode : function (utftext) {
    var string = "";
    var i = 0;
    var c = c1 = c2 = 0;

    while ( i < utftext.length ) {

        c = utftext.charCodeAt(i);

        if (c < 128) {
            string += String.fromCharCode(c);
            i++;
        }
        else if((c > 191) && (c < 224)) {
            c2 = utftext.charCodeAt(i+1);
            string += String.fromCharCode(((c & 31) << 6) | (c2 & 63));
            i += 2;
        }
        else {
            c2 = utftext.charCodeAt(i+1);
            c3 = utftext.charCodeAt(i+2);
            string += String.fromCharCode(((c & 15) << 12) | ((c2 & 63) << 6) | (c3 & 63));
            i += 3;
        }

    }
    return string;
}
}

var _q="15028799613985034465755506450771565229282832217860390155996483840017"
ibe_q=str2bigInt(_q,10,0) 

function printArray( a )
{
        if (a.length == 0)
        {
            document.write( "[]")
            document.write('<br>')
        }
        for ( var i=0; i< a.length; ++i)
        {
            document.write( bigInt2str(a[i],10,0))
            document.write('<br>')
        }
}
function printGTArray(a)
{
    printArray(a[0])
    printArray(a[1])
}

function gt2str(a)
{
	var str="";
	if(a.length == 0 )
		str=[]
	else
		{
			str+="["	
			for(var i=0;i<a.length;i++)
			{
				str+="["
				for(var j=0;j<a[i].length;j++)
				{
					str+="'"+bigInt2str(a[i][j],10,0)+"'"
					str+=","
				}
				str+="],"
			}
			str+="]"
		}
	return str
}

function g12str(a)
{
	var str="";
	if(a.length == 0 )
		str=[]
	else
		{
			str+="["	
			for(var i=0;i<a.length;i++)
			{
					str+="'"+bigInt2str(a[i],10,0)+"'"
					str+=","
			}
			str+="]"
		}
	return str
}

function printElem(anum)
{

            document.write( bigInt2str(anum,10,0))
            document.write('<br>')
}

function printMark(str)
{
   
        document.write( str )
        document.write('<br>')
}

function ascStr2BigInt(str)
{
    var i;
    m=""
    for(i=0;i<str.length;i++)
    {
        m += str.charCodeAt(i).toString(16)
    }
    return str2bigInt(m,16)
    
}

function G2BigInt(g)
{
    var gb=new Array(g.length)
    for(var i=0; i<g.length; ++i)
    {
        gb[i] = str2bigInt(g[i],10,0)
            
            //document.write( bigInt2str(gb[i],10,0))
            //document.write('<br>')
            //  
    }
    return gb
}

function GDup(g)
{
    var gb=new Array(g.length)
    for(var i=0; i<g.length; ++i)
    {
        gb[i] = dup(g[i])
    }
    return gb
}
function GMul(v,e)
{
    var ret = new Array(v.length)
    for(var i=0;i<v.length;++i)
    {
        ret[i]=fp_mult(v[i],e[i])
    }
    return ret

}

function GAdd(v,e)
{
    var ret = new Array(v.length)
    for(var i=0;i<v.length;++i)
    {
        ret[i]=fp_add(v[i],e[i])
    }
    return ret

}
function GSub(v,e)
{
    var ret = new Array(v.length)
    for(var i=0;i<v.length;++i)
    {
        ret[i]=fp_sub(v[i],e[i])
    }
    return ret

}
function GNeg(v)
{
    var ret = new Array(v.length)
    for(var i=0;i<v.length;++i)
    {
        ret[i]=fp_neg(v[i])
    }
    return ret

}

function GInvert(v)
{
    var ret = new Array(v.length)
    
    for(var i=0;i<v.length;++i)
    {
        ret[i]=inverseMod(v[i],ibe_q)
    }
    return ret

}

function GIsEqual(a,b)
{
    for(var i=0;i<a.length;++i)
    {
        if(!equals(a[i],b[i]))
        {
            return false;
        }
    }
    return true;

}
function GIsZero(a)
{
    for(var i=0;i<a.length;++i)
    {
        if(!isZero(a[i]))
        {
            return false;
        }
    }
    return true;

}





function fp_add(s1,s2)
{
    var s = add(s1,s2)
    if( greater(s,ibe_q) )
        s = sub(s,ibe_q)
    return s
}

function fp_sub(s1,s2)
{
    var s;
    if( greater(s2,s1) )
        s = sub(add(s1,ibe_q),s2)
    else
        s = sub(s1,s2)
    return s
}

function fp_sub_n(s1,s2)
{
    var s;
    if( greater(s2,s1) )
        s = sub(add(s1,ibe_q),s2)
    else
        s = sub(s1,s2)
    return s
}


function fp_invert(s)
{
    var ret = inverseMod(s,ibe_q)
    return ret 
}



function fp_mult(c3,c4)
{

    var _q="15028799613985034465755506450771565229282832217860390155996483840017"
    var q=str2bigInt(_q,10,0) 
    //var c=mult(c3,c4)
    //c = mod(c,ibe_q) 
    var c = multMod(c3,c4,ibe_q)
    return c 
}

function fp_neg(anum)
{
    var ret ;
    if(equalsInt(anum,0))
        ret = dup(anum)
    else
    {
        
        ret = sub(ibe_q,anum)
    }
    return ret 

}

function polymod_const_mul(a,e)
{
    var res = new Array(e.length)
    for( var i=0;i<e.length;++i)
    {
        res[i]=fp_mult(a,e[i] )
    }
    return res
}


function polymod_mul_degree3(e,f)
{

    var _xpwr=new Array(3)
    _xpwr[0]="3053610355725337299498468625544028297836124273177919204884624393825"
    _xpwr[1]="1595757413637099638012768355522018425276144655772136098584582477246"
    _xpwr[2]="6701335092867243227676401275323443222522968592352346660225596428403"
    var xpwr=G2BigInt(_xpwr)
    var _xpwr1=new Array(3)
    _xpwr1[0]="9385910079666998837875568805382738923761376323975517375834674752474"
    _xpwr1[1]="12727029633817405504618036300927848741686155698560986497611454569413"
    _xpwr1[2]="11293357710551192191735297347007133101291849005436098117914318596946"
    var xpwr1=G2BigInt(_xpwr1)

    var dst=new Array(3);


    var scratch = new Array(3);
    var c3 = fp_add(e[0],e[1])
    var c4 = fp_add(f[0],f[1])

    //document.write( bigInt2str(c3,10,0))
    //document.write('<br>')
    //document.write( bigInt2str(c4,10,0))
    //document.write('<br>')
    scratch[2]=fp_mult(c3,c4)

    c3 = fp_add(e[0],e[2])
    c4 = fp_add(f[0],f[2])
    scratch[1] = fp_mult(c3,c4)

    c3 = fp_add(e[1],e[2])
    c4 = fp_add(f[1],f[2])
    scratch[0] = fp_mult(c3,c4)

    //for ( var i=0; i< p2x.length; ++i)
    //{
    //    document.write( bigInt2str(scratch[i],10,0))
    //            document.write('<br>')
    //}

    dst[1] = fp_mult(e[1],f[1])
    dst[0] = fp_mult(e[0],f[0])
    c4 = fp_mult(e[2],f[2])
    c3 = fp_add(dst[1],c4)
    //c3=fp_sub(scratch[0],c3)
    c3=fp_sub(scratch[0],c3)

    //

    //document.write( bigInt2str(dst[1],10,0))
   //document.write( bigInt2str(c4,10,0))
    //document.write('<br>')

    dst[2] = fp_add(dst[0],c4)
    scratch[1] = fp_sub( scratch[1],dst[2])
    dst[2] = fp_add(dst[1],scratch[1])
    
    scratch[2] = fp_sub(scratch[2],dst[0])
    dst[1] = fp_sub(scratch[2],dst[1])


    //document.write( bigInt2str(xpwr1[0],10,0))
    //document.write('<br>')

    //p0 is always zeror . ignore following calc
    var p0 = new Array(3);

        //
    p0 = polymod_const_mul(c3,xpwr)
    dst = GAdd(dst,p0) 
    p0 = polymod_const_mul(c4,xpwr1)
    // 
    dst = GAdd(dst,p0) 
    return dst
}



function curve_double(Z)
{
    var ret = new Array(2)
    if (equalsInt(Z[1],0))
    {
        ret[1]=str2bigInt("0",10,0)
        return  ret
    }
    else
    {
       var x=Z[0]  
       var y=Z[1]

       var lambda=fp_mult(x,x)
       _a = "1871224163624666631860092489128939059944978347142292177323825642096"   
       var a = str2bigInt(_a,10,0)
       lambda = fp_mult(lambda,str2bigInt("3",10,0))
       lambda = fp_add(lambda,a)
       var e0 = fp_add(y,y)
       
        //bitSizeTest
        //document.write( bitSize(ibe_q))
        //document.write( bpe )
        //document.write('<br>')
       e0=inverseMod(e0,ibe_q)
       lambda = fp_mult(lambda,e0)
       var e1 = fp_add(x,x)
       e0 = fp_mult(lambda,lambda)
       e0 = fp_sub(e0,e1)
       e1 = fp_sub(x,e0)
       e1 = fp_mult(e1,lambda)
       e1 = fp_sub(e1,y)

       ret[0] = e0
       ret[1] = e1
        
     
       return  ret 
    }
    
}

function curve_mul(p,q)
{
    var e0 = fp_sub(q[0],p[0])
    var ret = new Array(2)
    ret[0] = int2bigInt(0,1,1)
    ret[1] = int2bigInt(0,1,1)

	
	if(GIsZero(p))
		return dup(q)
	if(GIsZero(q))
		return dup(p)
	
    if( isZero(e0) )
    {
        if( isZero(fp_sub(q[1],p[1])))
        {
           if(isZero( p[1]))
                return ret
            else
                return curve_double(p)
        }
        else
            return ret
    }
    else
        e0 = inverseMod(e0,ibe_q)
    var lambda = fp_sub(q[1],p[1])
    lambda = fp_mult(lambda,e0)
    e0 = fp_mult(lambda,lambda)
    e0 = fp_sub(e0,p[0])
    e0 = fp_sub(e0,q[0])
    
    e1 = fp_sub(p[0],e0)
    e1 = fp_mult(e1,lambda)
    e1 = fp_sub(e1,p[1])

    ret[0] = e0
    ret[1] = e1
    
    return ret
}

function d_miller_eval_fun(a,b,c,Qx,Qy)
{
    var e0 = new Array(2) 
    e0[0] = new Array(3)
    e0[1] = new Array(3)
    var d=3   
    for(i=0;i<d;++i)
    {
        e0[0][i] = fp_mult(Qx[i],a)
        e0[1][i] = fp_mult(Qy[i],b)
    }
    e0[0][0] = fp_add(e0[0][0],c)
    return e0
}

function fq_mul(a,b)
{
    var r = new Array(2) 
    var px = a[0]
    var py = a[1]
    var qx = b[0]
    var qy = b[1]

    var _nqrx=new Array(3)
    _nqrx[0]="142721363302176037340346936780070353538541593770301992936740616924"
    _nqrx[1]="0"  
    _nqrx[2]="0"
    nqrx = G2BigInt(_nqrx)
    
    var e0 = GAdd(px,py)
    var e1 = GAdd(qx,qy)
    
    var e2 = polymod_mul_degree3(e0,e1)
    e0 = polymod_mul_degree3(px,qx)
    e1 = polymod_mul_degree3(py,qy)
    r[0] = polymod_mul_degree3(e1,nqrx)
    r[0] = GAdd(r[0],e0)
    e2=GSub(e2,e0)
    r[1]=GSub(e2,e1)
    
    
    return r;
    
}

function poly_remove_leading_zeroes(e)
{
    var n = e.length - 1
    for( ; n >= 0; n--)
    {
        if( !isZero(e[n]) )
        {
            return ;
        }
        else
        {
            e.pop()
        }
    }
    return ;
}

function poly_div(a,b)
{
    var qr = new Array(2)

    //b degree is not zero.
    
    var n=b.length-1 
    var m=a.length-1
    //document.write( "poly_div:"+m+n )
    //document.write('<br>')
    if(n>m)
    {
       qr[0]=[]
       qr[1]=a
       return qr
    }
    var k = m-n
    var pr = GDup(a) 
    var pq = new Array(k+1)
    
    //document.write( "poly_div:"+m+n )
    //document.write('<br>')
    var e0
    var binv = fp_invert(b[n])
    while( k>= 0)
    {
        pq[k]=fp_mult(binv,pr[m])
        for( var i = 0; i<=n; ++i)
        {
            e0 = fp_mult(pq[k],b[i])
            pr[i+k]=fp_sub(pr[i+k],e0)
        }
    

        k=k-1
        m=m-1
    } 
    poly_remove_leading_zeroes(pr)
    qr[0]=pq
    qr[1]=pr
      
    return qr
}

function poly_mul(f,g)
{
    var r = []
    var fcount=f.length
    var gcount=g.length
    if( fcount == 0 || gcount ==0 )
        return r
    var n = fcount+gcount-1
    var e0
    r = new Array(n)
    
        //document.write( "poly_mul "+n+fcount+gcount )
        //document.write('<br>')
    for( var i=0;i<n;++i)
    {
        r[i]= str2bigInt("0",10,0)
        for( var j=0;j<=i;++j)
        {
            if (j < fcount && i - j < gcount)
            {
                e0 = fp_mult(f[j],g[i-j])
                r[i] = fp_add(r[i],e0)
            }
            
        }
    }
    poly_remove_leading_zeroes(r) 
    return r
}
//in place res
function poly_const_mul(res,a,poly)
{
    var n=poly.length
    for(var i=0;i<n;i++)
    {
        res[i] = fp_mult(a,poly[i])
        
        //document.write( "exit " )
        //document.write('<br>')
    
        //document.write( "exit " )
        //document.write('<br>')
    }
    poly_remove_leading_zeroes(res)
}

function poly_sub(f,g)
{
    var diff
    var n = f.length
    var n1 = g.length
    var big

    var is_f_Big = false
    
    if( n > n1)
    {
       big = dup(f) 
       n = n1
       n1 = f.length
       is_f_Big = true
    }
    else
    {
        big = dup(g)
    }
    
    diff = new Array(n1)

    var i = 0
    for ( i=0;i<n;++i)
    {
        // 1-bigInt miss 9999. have to make a fp_sub_n version. makeup the 9999
        diff[i]=fp_sub_n(f[i],g[i])
    }
    for( ; i<n1;++i)
    {
        if(is_f_Big)
        {
            diff[i]=dup(big[i])
        }
        else
        {
            diff[i]=fp_neg(big[i])
        }
    }
    
    return diff 
}



function polymod_invert(a)
{
    var out=new Array(3);
    var _p = new Array(4);
    
    _p[0]="11975189258259697166257037825227536931446707944682470951111859446192"
    _p[1]="13433042200347934827742738095249546804006687562088254057411901362771"
    _p[2]="8327464521117791238079105175448122006759863625508043495770887411614"
    _p[3]="1"
    
    //var p = G2BigInt(_p)

    var r0 = G2BigInt(_p)
    var r1 = dup(a)
    var r2 = []
    var q = []
    var b0 = []
    var b1 = new Array(1)
    b1[0] = int2bigInt(1,1,1)
    var b2

    for(;;)
    {
        var qr = poly_div(r0,r1) 
        q=qr[0]
        r2=qr[1]
        if( r2.length == 0) break;
        b2=poly_mul(b1,q)
        
        b2=poly_sub(b0,b2)
        b0=dup(b1)
        b1=dup(b2)
        r0=dup(r1)
        r1=dup(r2)

        
        //document.write( "poly_div one round " )
        //document.write('<br>')
    }
    
        //document.write( "poly_div after " )
        //document.write('<br>')
    
    
    var inv=fp_invert(r1[0])
    //document.write( "before out calc:" )
    //document.write('<br>')
    poly_const_mul( out, inv, b1)
    
    return out 
    //return a 
}

function fq_invert(a)
{
    var r= new Array(2);

    var _nqrx=new Array(3)
    _nqrx[0]="142721363302176037340346936780070353538541593770301992936740616924"
    _nqrx[1]="0"
    _nqrx[2]="0"
    nqrx = G2BigInt(_nqrx)

    e0 = polymod_mul_degree3(a[0],a[0])
    e1 = polymod_mul_degree3(a[1],a[1])
    e1 = polymod_mul_degree3(e1,nqrx)
    e0 = GSub(e0,e1)
        //document.write( "fq_invert" )
        //document.write('<br>')
        
        //document.write( "fq_invert" )
        //document.write('<br>')
    e0 = polymod_invert(e0)
    r[0] = polymod_mul_degree3(a[0],e0)
    e0 = GNeg(e0)
    r[1] = polymod_mul_degree3(a[1],e0)
    
    return r 
}

function polymod_is0(a)
{
    for(var i=0; i<a.length;i++)
    {
        if(!isZero(a[i]))
            return false;
    } 
    return true;
}

function polymod_is1(a)
{
    var n=a.length
    if(n == 0)
        return false
    if(!equalsInt(a[0],1)) return false;
    for(var i=1;i<n; i++)
    {
        if(!isZero(a[i])) return false;
    }
    
    return true;
    //a[i] 
}

function polymod_double(a)
{
    var res = new Array(a.length)
    for(var i=0; i<a.length;i++) 
    {
        res[i]=fp_add(a[i],a[i])
    }
    return res
}

function polymod_sub(e,f) 
{
    var r = new Array(e.length);
    for(var i=0; i<e.length; ++i)
    {
        r[i]=fp_sub(e[i],f[i])
    }
    return r 
}

function polymod_halve(a)
{
    var e0 = new Array(3)
    e0[0]=str2bigInt("7514399806992517232877753225385782614641416108930195077998241920009",10,0)
    e0[1]=str2bigInt("0",10,0)
    e0[2]=str2bigInt("0",10,0)
    var r = polymod_mul_degree3(a,e0)
    return r
}

function lucas_even(a, cofactor)
{
    //if( a[0] 
    if(polymod_is1(a[0]) && polymod_is0(a[1]))
        // Be ware I haven't make a dup
        return a
    var out = new Array(2);
    var t0 = new Array(3);
    t0[0] = str2bigInt("2",10,0)
    t0[1] = str2bigInt("0",10,0)
    t0[2] = str2bigInt("0",10,0)
    var t1=polymod_double(a[0])
    
    out[0]=GDup(t0)
    out[1]=GDup(t1)

    cofactorStr = bigInt2str(cofactor,2)
    j = cofactorStr.length - 1
    for(;;)
    {
        if(!j)
        {
            out[1]=polymod_mul_degree3(out[0],out[1])
            out[1]=GSub(out[1],t1)
            out[0]=polymod_mul_degree3(out[0],out[0])
            out[0]=GSub(out[0],t0)
            break;
        }
        if( cofactorStr.charAt(cofactorStr.length-j-1) == '1')
        {
            
            out[0]=polymod_mul_degree3(out[0],out[1])
            out[0]=GSub(out[0],t1)
            out[1]=polymod_mul_degree3(out[1],out[1])
            out[1]=GSub(out[1],t0)
        }
        else
        {
            out[1]=polymod_mul_degree3(out[0],out[1])
            out[1]=GSub(out[1],t1)
            out[0]=polymod_mul_degree3(out[0],out[0])
            out[0]=GSub(out[0],t0)
        }
        j--;
        
    }

   
    
    out[0]=polymod_double(out[0])
    a[0]=polymod_mul_degree3(t1,out[1])
    a[0]=GSub(a[0],out[0])
    
    t1 = polymod_mul_degree3(t1,t1)
    t1 = GSub(t1,t0)
    t1 = GSub(t1,t0)

    
    
    
    out[0]=polymod_halve(out[1])
    var t1inv=polymod_invert(t1)
    out[1]=polymod_mul_degree3(a[0],t1inv)
    out[1]=polymod_mul_degree3(out[1],a[1])

    return out
}


function cc_tatepower( _in)
{
    var out;
    var _xpowq = new Array(3)
    _xpowq[0]="657521270017796069346395138181635563647395275435524050257477505788"
    _xpowq[1]="6866761136669758413861832255861003032305625478275258872526688545352"
    _xpowq[2]="2015629970386633557539271384842840627883763896393847647101244719938"
    var xpowq=G2BigInt(_xpowq)
    var _xpowq2 = new Array(3)
    _xpowq2[0]="7680052371975202795937705303411295551244651607969534772653536375608"
    _xpowq2[1]="11929925182031872553846797980141412727270917535480437433607306713575"
    _xpowq2[2]="8162038477315276051893674194910562196977206739585131283469795294664"
    var xpowq2=G2BigInt(_xpowq2)

    var e0 = new Array(2),e2 = new Array(3),e3 = new Array(2)
    var e0re,e0im  
    var e0re0,e0im0
    var _inre = _in[0]
    var _inim = _in[1]

    function qpower(sign)
    {
       e2 = polymod_const_mul(_inre[1],xpowq) 
       e0re = e2 

       e2 = polymod_const_mul(_inre[2],xpowq2) 
       e0re = GAdd(e0re,e2)

       e0re0 = e0re[0] 
       e0re0 = fp_add(e0re0,_inre[0])
    
       e0re[0] = e0re0
       e0[0]=e0re
       if(sign > 0)
        {
            e2 = polymod_const_mul(_inim[1],xpowq) 
            e0im = e2

            e2 = polymod_const_mul(_inim[2],xpowq2)
            e0im = GAdd(e0im,e2)
        
            e0im0 = e0im[0] 
            e0im0 = fp_add(e0im0,_inim[0])
            
            e0im[0] = e0im0
            e0[1] = e0im

        } 
        else
        {
            e2 = polymod_const_mul(_inim[1],xpowq) 
            e0im = GNeg(e2)

            e2 = polymod_const_mul(_inim[2],xpowq2)
            e0im = GSub(e0im,e2)
            
            e0im0 = e0im[0] 
            e0im0 = fp_sub(e0im0,_inim[0])

            e0im[0] = e0im0
            e0[1] = e0im
            
        }

    
    }

    qpower(1)
    

    //be ware of here . e3 = e0 doesn't work at all.
    //e3 = e0
    e3[0] = e0[0]
    e3[1] = e0[1]
    e0re = _in[0]
    e0im = GNeg(_in[1])
    
    
    e0[0] = e0re
    e0[1] = e0im
        
   // printArray(e0[0])
    
        //document.write( "fq_mul_begin" )
        //document.write('<br>')
    e3 =fq_mul(e3,e0)
        //document.write( "fq_mul_end" )
        //document.write('<br>')

    qpower(-1)
    e0 = fq_mul(e0,_in)
    e0 = fq_invert(e0)
    _in = fq_mul(e3,e0)
    
    e0[0] = _in[0]
    e0[1] = _in[1]

    
    
    var phikonr = str2bigInt("15028799613985034465755506450771569105982409691595259672696426485013",10,0)
    out = lucas_even(e0,phikonr)
    
    return out
    //return _in
    
}

function pairing(Px,Py,p2x,p2y)
{

    var out;
    _nqrinv=new Array(3)
    _nqrinv[0]="6041968486146819522833566161674844805011295865114179686064601307785"
    _nqrinv[1]="0"
    _nqrinv[2]="0"
    nqrinv = G2BigInt(_nqrinv);

    _nqrinv2= new Array(3)
    _nqrinv2[0]="12869220911900321812241940612176383961168937626526543351701949451131"
    _nqrinv2[1]="0"
    _nqrinv2[2]="0"
    nqrinv2 = G2BigInt(_nqrinv2);

    var Qx=polymod_mul_degree3(p2x,nqrinv) 
    var Qy=polymod_mul_degree3(p2y,nqrinv2)

    var _cca="1871224163624666631860092489128939059944978347142292177323825642096"
    var cca = str2bigInt(_cca,10,0)

    function do_tangent()
    {
        
            //document.write( bigInt2str(q,10,0))
            //document.write('<br>')
            //addInt_(Zx,100)
           a = fp_mult(Zx,Zx)
           a = fp_mult(a,str2bigInt("3",10,0))
           a = fp_add(a,cca)
           a = fp_neg(a) 
           b = fp_add(Zy,Zy)
           t0 = fp_mult(b,Zy)
           c = fp_mult(a,Zx)
           c = fp_add(c,t0)
           c= fp_neg(c)
           e0=d_miller_eval_fun(a,b,c,Qx,Qy) 
           v = fq_mul(v,e0)
           vx = v[0]
           vy = v[1]
    }

    function do_line()
    {
       b=fp_sub(Px,Zx) 
       a=fp_sub(Zy,Py)
       t0=fp_mult(b,Zy)
       c=fp_mult(a,Zx)
       c=fp_add(c,t0)
       c=fp_neg(c)
       e0=d_miller_eval_fun(a,b,c,Qx,Qy)

       v=fq_mul(v,e0)
       vx = v[0]
       vy = v[1]
        

    }
    var P = new Array(2)
    P[0] = Px
    P[1] = Py

    var Zx=dup(Px)
    var Zy=dup(Py)
    var Z=new Array(2)
    Z[0]=Zx
    Z[1]=Zy

    var _vx = new Array(3)
    _vx[0]="1"
    _vx[1]="0"
    _vx[2]="0"
    var vx = G2BigInt(_vx)
    var _vy = new Array(3)
    _vy[0]="0"
    _vy[1]="0"
    _vy[2]="0"
    var vy = G2BigInt(_vy)
    var v = new Array(2)
    v[0] = vx
    v[1] = vy
        

    var q=str2bigInt("15028799613985034465755506450771561352583254744125520639296541195021",10,0)
    var a
    var b
    var c
    var t0
    var e0
    //mpz size of q
    var m = 222
    var m_total = 224
    //var m_str = '10001110101101001111110011110101111010000011000110101100011110101011010110010001100011010110101010110110001000011010111101011010011001101001000110111011100111000011010001100100100011110010001001011001010001100111101100001101'
    var m_str = bigInt2str(q,2)
    //var m=1
    
    for(;;)  
    {
        do_tangent() 
        if(!m) break;
        //if(m==218) break;
        //element_double
        Z=curve_double(Z)
        Zx = Z[0]
        Zy = Z[1]
        
        //document.write( m + m_str.charAt(m_total-m-1))
        //document.write('<br>')
        //simple use this as tstbits
        if( m_str.charAt( m_total-m-1 ) == '1' )
        {
         do_line()
         Z=curve_mul(Z,P) 
         Zx=Z[0]
         Zy=Z[1]

        }

        m--
    

        v=fq_mul(v,v) 
        vx = v[0]
        vy = v[1]

        
    }
    
    out = cc_tatepower(v)

    return out
}
function G2_curve_double(Z)
{
    var ret = new Array(2)

    
       var x=Z[0]  
       var y=Z[1]
    if( GIsZero(x) && GIsZero(y) )
        return Z

       var lambda=polymod_mul_degree3(x,x)
       var _a =new Array(3)
       _a[0]= "814666024090928804996017557078651267356185679871471934426494531496"   
       _a[1]="0"
       _a[2]="0"
       var a = G2BigInt(_a)
       lambda = polymod_const_mul(str2bigInt("3",10,0),lambda)
    
       lambda = GAdd(lambda,a)
       var e0 = polymod_double(y)

       e0 = polymod_invert(e0)
       //var _q="15028799613985034465755506450771565229282832217860390155996483840017"
       //var q=str2bigInt(_q,10,0) 
       //
       // //bitSizeTest
       // //document.write( bitSize(q))
       // //document.write( bpe )
       // //document.write('<br>')
       //e0=inverseMod(e0,q)
       lambda = polymod_mul_degree3(lambda,e0)
       var e1 = polymod_double(x)
       e0 = polymod_mul_degree3(lambda,lambda)
       e0 = polymod_sub(e0,e1)
       e1 = polymod_sub(x,e0)
       e1 = polymod_mul_degree3(e1,lambda)
       e1 = polymod_sub(e1,y)

       ret[0] = e0
       ret[1] = e1
        
       return  ret
    
}


function G2_curve_mul(p,q)
{
    var ret = new Array(2)
    if(GIsZero(p[0]) && GIsZero(p[1]))
    {    
        ret[0] = GDup(q[0])
        ret[1] = GDup(q[1])
        return GDup(q)
    }
    
    if( GIsEqual(p[0],q[0]) && GIsEqual(p[1],q[1]) )
    {
        
        return G2_curve_double(p) 
    }
    else
    {

    var e0 = polymod_sub(q[0],p[0])
    e0 = polymod_invert(e0)


    var lambda = polymod_sub(q[1],p[1])
    lambda = polymod_mul_degree3(lambda,e0)
    e0 = polymod_mul_degree3(lambda,lambda)
    e0 = polymod_sub(e0,p[0])
    e0 = polymod_sub(e0,q[0])
    //
    e1 = polymod_sub(p[0],e0)
    e1 = polymod_mul_degree3(e1,lambda)
    e1 = polymod_sub(e1,p[1])

    ret[0] = e0
    ret[1] = e1
    
    return ret
    }
}
function G2_build_pow_window(a,k)
{
    var sz = 16
    
   var a_lookup = new Array(16)

   //a_lookup[0] is not used
   a_lookup[1]=new Array(2)
   a_lookup[1][0]=GDup(a[0])
   a_lookup[1][1] =GDup(a[1])

   for(var s=2;s<sz;s++)
   {
       a_lookup[s]=G2_curve_mul(a_lookup[s-1],a)
    }

   return a_lookup
}


function GT_build_pow_window(a,k)
{
    var sz = 16
    
   var a_lookup = new Array(16)

   a_lookup[0]=new Array(2)
   a_lookup[0][0] = new Array(3)
   a_lookup[0][0][0]=int2bigInt(1,1,1)
   a_lookup[0][0][1]=int2bigInt(0,1,1)
   a_lookup[0][0][2]=int2bigInt(0,1,1)
   a_lookup[0][1] = new Array(3)
   a_lookup[0][1][0]=int2bigInt(0,1,1)
   a_lookup[0][1][1]=int2bigInt(0,1,1)
   a_lookup[0][1][2]=int2bigInt(0,1,1)

   for(var s=1;s<sz;s++)
   {
       a_lookup[s]=fq_mul(a_lookup[s-1],a)
    }

   return a_lookup
}

function build_pow_window_extract(a,k)
{
    var sz = 16
    
   var a_lookup = new Array(sz)

   a_lookup[0] = new Array(2)
   a_lookup[0][0]=int2bigInt(0,1,1)
   a_lookup[0][1] = int2bigInt(0,1,1)

   a_lookup[1] = GDup(a)
   for(var s=2;s<sz;s++)
   {
       a_lookup[s]=curve_mul(a_lookup[s-1],a)
    }

   return a_lookup
}

function element_pow_wind_extract(x,n)
{
   //pow 0 raise error later 
    
   var result = new Array(2)
   result[0] = int2bigInt(0,1,1)
   result[1] = int2bigInt(0,1,1)

   var k = 4

   var a_lookup = build_pow_window_extract(x)

   var nstr = bigInt2str(n,2)

    var inword,s;
    var word=0;
    var wbits=0
   for(inword=0,s=nstr.length-1;s>=0;s--)
   {
       var bit=(nstr.charAt( nstr.length-s-1 ) == '1')
       result = curve_mul(result,result)

       if(!inword && !bit)
            continue
         
       if(bit)
           bit = 1
        else
            bit = 0
    
      if(!inword)
      {
        inword=1;
        word=1
        wbits=1
      }
      else
      {
        word = word*2+bit
        wbits++
      }
    if (wbits == k || s == 0) { 
		
        result = curve_mul(result,a_lookup[word])
        inword = 0
        
    }
        
   }


   return result 

}



function build_pow_window_G1(a,k)
{
    var sz = 4
    
   var a_lookup = new Array(4)

   a_lookup[0] = new Array(2)
   a_lookup[0][0]=int2bigInt(0,1,1)
   a_lookup[0][1] = int2bigInt(0,1,1)

   a_lookup[1] = GDup(a)
   for(var s=2;s<sz;s++)
   {
       a_lookup[s]=curve_mul(a_lookup[s-1],a)
       printMark("a_lookup")
       printArray(a_lookup[s])
    }

   return a_lookup
}
//it takes 5 seconds...
function G2_pow(x,n)
{
   //pow 0 raise error later 
    
   var result = new Array(2)
   result[0] = new Array(3)
   result[0][0]=int2bigInt(0,1,1)
   result[0][1]=int2bigInt(0,1,1)
   result[0][2]=int2bigInt(0,1,1)
   result[1] = new Array(3)
   result[1][0]=int2bigInt(0,1,1)
   result[1][1]=int2bigInt(0,1,1)
   result[1][2]=int2bigInt(0,1,1)

   var k = 4

   var a_lookup = G2_build_pow_window(x,k)

   var nstr = bigInt2str(n,2)

    var inword,s;
    var word=0;
    var wbits=0
   for(inword=0,s=nstr.length-1;s>=0;s--)
   {
       var bit=(nstr.charAt( nstr.length-s-1 ) == '1')
       result = G2_curve_double(result,result)
       if(!inword && !bit)
            continue
         
       if(bit)
           bit = 1
        else
            bit = 0
    
      if(!inword)
      {
        inword=1;
        word=1
        wbits=1
      }
      else
      {
        word = word*2+bit
        wbits++
      }
    if (wbits == k || s == 0) { 
        result = G2_curve_mul(result,a_lookup[word])
        inword = 0
        
    }
        
   }


   return result 

}


function GT_pow(x,n)
{
   //pow 0 raise error later 
    
   var result = new Array(2)
   result[0] = new Array(3)
   result[0][0]=int2bigInt(1,1,1)
   result[0][1]=int2bigInt(0,1,1)
   result[0][2]=int2bigInt(0,1,1)
   result[1] = new Array(3)
   result[1][0]=int2bigInt(0,1,1)
   result[1][1]=int2bigInt(0,1,1)
   result[1][2]=int2bigInt(0,1,1)

   var k = 4

   var a_lookup = GT_build_pow_window(x)

   var nstr = bigInt2str(n,2)

    var inword,s;
    var word=0;
    var wbits=0
   for(inword=0,s=nstr.length-1;s>=0;s--)
   {
       var bit=(nstr.charAt( nstr.length-s-1 ) == '1')
       result = fq_mul(result,result)

       if(!inword && !bit)
            continue
         
       if(bit)
           bit = 1
        else
            bit = 0
    
      if(!inword)
      {
        inword=1;
        word=1
        wbits=1
      }
      else
      {
        word = word*2+bit
        wbits++
      }
    if (wbits == k || s == 0) { 
        result = fq_mul(result,a_lookup[word])
        inword = 0
        
    }
        
   }


   return result 

}

function element_pow_wind_G1(x,n)
{
   //pow 0 raise error later 
    
   var result = new Array(2)
   result[0] = int2bigInt(0,1,1)
   result[1] = int2bigInt(0,1,1)

   var k = 2

   var a_lookup = build_pow_window_G1(x)

   var nstr = bigInt2str(n,2)

    var inword,s;
    var word=0;
    var wbits=0
   for(inword=0,s=nstr.length-1;s>=0;s--)
   {
       var bit=(nstr.charAt( nstr.length-s-1 ) == '1')
       result = curve_mul(result,result)

       if(!inword && !bit)
            continue
         
       if(bit)
           bit = 1
        else
            bit = 0
    
      if(!inword)
      {
        inword=1;
        word=1
        wbits=1
      }
      else
      {
        word = word*2+bit
        wbits++
      }
    if (wbits == k || s == 0) { 
        result = curve_mul(result,a_lookup[word])
        inword = 0
        
    }
        
   }


   return result 

}

function jacobi(a,n)
{
    var bone = int2bigInt(1,1,1)
    var btwo = int2bigInt(2,2,1)
    //var beight = int2bigInt(8,4,1)
            
    if (isZero(a))
    {
        return  0
    }
    if (equalsInt(a,1))
        return  1
    if (equalsInt(a,2))
    {
        var n8 = modInt(n,8)
        if(n8 == 3 || n8 == 5)
        {
            return -1
        }
        else    
        {
            return 1  
        }
    }

    if(modInt(a,2)==0)
    {
        var ad2 =dup(a)
        var ar =dup(a)
        divide_( a, btwo, ad2,ar )
        return jacobi(btwo,n) * jacobi(ad2,n)
    }
    
    if(greater(a,n))
    {
        var ad2 =dup(a)
        var ar =dup(a)
        divide_( a, n, ad2,ar )
        return jacobi(ar,n)
    }
    
    if(modInt(a,4) == 3 && modInt(n,4) == 3)
    {
        return -1*jacobi(n,a)
    }
    else
        return jacobi(n,a)
    
}

function legendre_q(a)
{
    
    var qm1d2 = str2bigInt("7514399806992517232877753225385782614641416108930195077998241920008",10,0)
    var qm1 = str2bigInt("15028799613985034465755506450771565229282832217860390155996483840016",10,0)
    var ls=powMod(a,qm1d2,ibe_q)
    
    if(isZero(a))
        return 0
    
    if( equalsInt(ls,qm1) )
         return -1
    
    else
        return 1
}

function mod_sqrt(a,p)
{
    if(isZero(a))
        return int2bigInt(0,1,1)
    else if (equalsInt(p,2))
        return p
    //else if p%4==3 return pow(a,(p+1)/4,p)

    var p = str2bigInt("15028799613985034465755506450771565229282832217860390155996483840017",10,0)
    //var s = str2bigInt("15028799613985034465755506450771565229282832217860390155996483840016",10,0)
    // pre calculated.
    var e = 3 

    var n = 5
    var sp1d4 = str2bigInt("469649987937032327054859576586611413415088506808137192374890120001",10,0)
    var s = str2bigInt("939299975874064654109719153173222826830177013616274384749780240001",10,0)
    var stwo = int2bigInt(2,2,1)
    
    var x=powMod(a,sp1d4,p)
    var b=powMod(a,s,p)
    var g=powMod(str2bigInt("5",10,0),s,p)
    var r = 4
    for(;;)
    {
        var t = dup(b)
        var m = 0;
        for(;m<r;++m)
        {
            if(equalsInt(t,1))
                break;
            t = multMod(t,t,p)
        }
        if( m == 0) 
        {
            return x
        }
        
        
        var rmm1 = powMod(stwo,int2bigInt( r-m-1,4,1 ), p)
        var gs = powMod(g,rmm1,p)
        g =  multMod(gs,gs,p)
        x = multMod(x,gs,p)
        b = multMod(b,g,p)
        r=m
    }


    

}

function G1_from_hash(a)
{
    
    //var x=str2bigInt("3824322377327390281075901559054753441969158872320107172509333127642",10,0)
    //var x=str2bigInt("5810624218142754477456276241355967585043855821381859799690296306626",10,0)
    //var x=str2bigInt("0160c2f88e5e4e7c6bdffa26d6a7ecd42b2db84b000160c2f88e5e4e",16,0)

    
    var s0=ibe_hash( String.fromCharCode(1,0,0,0,0,0,0,0)+a)
    //to little endian
    var mcord=[6,6,2,2,-2,-2,-6,-6]
    var s1 = ""
    for(var i=0;i<s0.length;++i)
        s1+=s0[mcord[i%8]+i]

    //H || 0 || H || 1 || 
    //total 28 Byte
    var s=s1+"00"+s1.substr(0,14)
    
    //to bigInt
    var x=str2bigInt(s,16,0)
    if(greater(x,ibe_q))
        rightShift_(x,1)
    var t;
    var a = str2bigInt("1871224163624666631860092489128939059944978347142292177323825642096",10,0)
    var b = str2bigInt("9795501723343380547144152006776653149306466138012730640114125605701",10,0)

    var cofac = str2bigInt("9795501723343380547144152006776653149306466138012730640114125605701",10,0)
    
    for(;;)
    {
        t=fp_mult(x,x)
        t=fp_add(t,a)
        t=fp_mult(t,x) 
        t=fp_add(t,b)
        if( jacobi(t,ibe_q) == 1 ) break;
        //if( legendre_q(t) == 1 ) break;
        x = fp_mult(x,x) 
        x = addInt(x,1)
    } 
    var y = mod_sqrt(t,ibe_q)
    var yn = fp_neg(y)
    //if( greater(yn,y) )
        y=yn
    
   // printElem(y)
    
    var ret = new Array(2)
    ret[0] = x
    ret[1] = y
    
    //seems no need to do pow_wind_G1, just return
    //ret = element_pow_wind_G1(ret,cofac)

    return ret
}

function gen_U(r)
{
    var _px=new Array(3)

    _px[0]="13811081979843030123575683961364195098182780905035434741449961170701"
    _px[1]="5168311754219690299065397857137804743287622694314500894713928555910"
    _px[2]="8811934331084896044063754515309978334585216131609973100543622590549"
    var _py=new Array(3)
    _py[0]="11978937640305627329722610355100010500665621620036973046712737173409"
    _py[1]="4386115112854559530338202238348812530267878704872566762635368727761"
    _py[2]="10391044986192973973988118337245431673037549976707601333607548174896"

    var px=G2BigInt(_px)
    var py=G2BigInt(_py)
    var p=new Array(2)
    p[0]=px
    p[1]=py

    var U = G2_pow(p,r)
    var k = 4
    //var a_lookup = G2_build_pow_window(p,k)

	return U


}

function xor(str,key)
{
	var encStr="";
	for(var i=0;i<str.length;i++)
	{
		encStr+=String.fromCharCode( str.charCodeAt(i) ^ key.charCodeAt(i%key.length) )
	}
	return encStr
}

function aes_encode(str,key)
{
    var encrypted = CryptoJS.AES.encrypt(str, key, { mode:CryptoJS.mode.CTR });
    return encrypted
}
function aes_decode(encrypted,key)
{
    var decrypted = CryptoJS.AES.decrypt(encrypted, key, { mode:CryptoJS.mode.CTR });
    return Base64.decode(decrypted.toString(CryptoJS.enc.Base64))
}

function array_to_G2( strArray )
{
	var ret = new Array(2)
	for( var i=0;i<2;i++)
	{
		ret[i] = new Array(3)
		for( var j=0;j<3;j++)
		{
			ret[i][j]=str2bigInt(strArray[i][j],10,0)
		}	
	}
	return ret
}

function array_to_G1( strArray)
{
	
	var ret = new Array(2)
	for( var i=0;i<2;i++)
	{
		ret[i] = str2bigInt(strArray[i],10,0)
	}
	return ret
}

//encryption interface
//id is identity of target user
function ibe_encrypt(id,msg)
{
    var _p2x=new Array(3) 
    _p2x[0]="8733743139883721929746557669281786776630567016143461292221315656826"
    _p2x[1]="8361394066264508648455507973062910774845860829356344049728407408780" 
    _p2x[2]="10875262355316927425360895615220150789510813104233695541722171619177"
    var _p2y= new Array(3)
    _p2y[0]="10447339307901630518074865526175395285504103515763147836036408151730"
    _p2y[1]="5624160785336662084843147096952829593564757784171941592985688526173"
    _p2y[2]="3410094274429991793295974722413474163646214393604192093427842333867"



    var p2x=G2BigInt(_p2x)
    var p2y=G2BigInt(_p2y)

    // if the input id is '', it's not possible to do encryption. just return
    if( id == '')
        return ''
    
    var Q_id = G1_from_hash(id)

    var gt = pairing(Q_id[0],Q_id[1],p2x,p2y) 
    //var r = str2bigInt("2843629013705221760874038394476758957859008618996765624028037636473",10,0)
	var r = randBigInt(223,0)
	var U = gen_U(r)

        var enc=GT_pow(gt,r)
	encKey = ibe_hash(gt2str(enc))
	//var encMsg = Base64.encode(xor(msg, encKey))
        var encMsg = aes_encode(msg,encKey)

	//var ret = "var encMsg = Base64.decode('" + encMsg +"');"
	var ret = "var encMsg = ('" + encMsg +"');"
	ret += "var U = array_to_G2("+gt2str(U)+")"

        //hide the details using base64
	return Base64.encode( ret )

}

//decryption interface
function ibe_decrypt(secretKeyJson,msgJson)
{
	//eval the json text
	//here will get:
	//encMsg
        //U
        //we have to do replacing. Base64.decoding including '\n'.
        msgJson = Base64.decode(msgJson).replace(/\n/g,"")
	eval(msgJson)

	//here will get:
	//d_id
	eval(Base64.decode(secretKeyJson))

    var gt = pairing(d_id[0],d_id[1],U[0],U[1]) 
	decKey=ibe_hash(gt2str(gt))
	//msg = xor(encMsg,decKey)
        msg = aes_decode(encMsg,decKey)
	return msg
}
