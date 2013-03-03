ibejs - Identity Based Encryption Javascript library.  
===

0. the ibe_extract.py depends on ibe_extract.js and node.js
install node.js before use it.

1. Generating of Secret Key
//code
secretKeyOfUserB=ibe_extract("UserB@gmail.com")
//run with node.js. Output is secret key of UserB@gmail.com
node ibe_encrypt.js UserB@gmail.com

2. The ibe process:
UserA want to send a email to UserB and encrypt the email using IBE.

1) UserA use ibe_encrypt() which is in ibe.js 
enc_msg=ibe_encrypt("the message user a wanna send to UserB","UserB@gmail.com") 
2) the enc_msg are sended to UserB
3) UserB receive the enc_msg
4) UserB request his secret key from server. First UserB should pass authentication. Then your server use ibe_encrypt.py to extract the secret key: secretKeyOfUserB. and send to UserB
5) UserB use ibe_decrypt which is in ibe.js
msg = ibe_decrypt(enc_msg,secretKeyOfUserB)
6) UserB are able to read msg from UserA now

3. About the random oracles
Boneh-Franklin IBE scheme supposes two hash function is random oracles
here SHA512 is used, SHA512's first 160 bits is choosen.
