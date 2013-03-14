ibejs - Identity Based Encryption Javascript library.  
===

Dependencies
---

install node.js in order to run demo.
  

Generating of Secret Key
---

	secretKeyOfUserB=ibe_extract("UserB@gmail.com")
	#run with node.js. Output is secret key of UserB@gmail.com
	$node ibe_extract.js userb@gmail.com
	dmFyIGRfaWQgPSBhcnJheV90b19HMShbJzM2NDc3OTgzNjMyNDMxNDcwMDA1NDE3MTUyNjcwMTUwNDA4NTA5NDkyNzkwNDk1Mzk5OTk2OTM1NTE0NzgyMTM2NjUnLCc2NzIwMzY3NzAzMTk1NjkyMzkwNzM4NjM0MDU3MTA1OTAzODE3MzUyODc5OTgyMjgwMTcxNjQ2Mjk0NDk3NzY0MCcsXSk7

The ibe process:
---
UserA want to send a email to UserB and encrypt the email using IBE.

1. UserA use ibe_encrypt() which is in ibe.js 
enc_msg=ibe_encrypt("the message user a wanna send to UserB","UserB@gmail.com") 
2. the enc_msg are sended to UserB
3. UserB receive the enc_msg
4. UserB request his secret key from server. First UserB should pass authentication. Then your server use ibe_encrypt.py to extract the secret key: secretKeyOfUserB. and send to UserB
5. UserB use ibe_decrypt which is in ibe.js
msg = ibe_decrypt(enc_msg,secretKeyOfUserB)
6. UserB are able to read msg from UserA now

About the random oracles
---
Boneh-Franklin IBE scheme supposes two hash function is random oracles
here SHA512 is used, SHA512's first 160 bits is choosen.
