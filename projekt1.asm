;Patryk Wegrzyn, Asemblery 2017
;Projekt1, SSH Fingerprint
;Modyfikacja: ruch skoczka
 
.286	;pusha, popa, operacje bitowe
 
;************DANE*****************************************************************
 
data1 segment
 
	Buffer db 300 dup("$")      ; tablica w ktorej, w ktorej przetrzumuje kolejne argumenty odzielone dolarem
	ArgCounter db 0             ; licznik argumentow dostarczonych do programu
	ArgLengths db 150 dup(0)    ; tablica w ktorej przetrzumuje dlugosci (ilosci znakow) kolejnych argumentow
	NewLine db 10,"$"   		;przejscie do nowej lini
	WrongArgNumb db "Nieprawidlowa ilosc argumentow! Oczekiwano 2 argumenty.",10,13,"$"
	WrongArg1 db "Nieprawidlowy format flagi modyfikacji! Oczekiwano 0 lub 1.",10,13,"$"
	WrongArg2Len db "Nieprawidlowa dlugosc wprowadzonego skrotu! Oczekiwano 32 znaki.",10,13,"$"
	WrongArg2Form db "Nieprawidlowe znaki we wprowadzonym skrocie!",10,13,"$"
	TopLine db "+----ASCII-Art----+",10,13, '$'
	BottomLine db "+-----------------+",10,13, '$'
	Modification db ?			;miejsc w pamieci do przechowywania flagi modyfikacji
	Array db 153 dup(0)			;glowna tablicy fingerprint'a dla gonca, domyslnie zapelniona zerami, bo jesli skoczek ani raz nie pojawi sie na polu, to wartosc pola nie zostanie zmieniona
	Converted db 16 dup(?)		;miejsce na przekonwertowany skrot do postaci binarnej
	ASCIItable db '.', 'o', '+', '=', '*', 'B', 'O', 'X', '@', '%', '&', '#', '/', '^'	;tablica znakow ascii, wymagana to konwersji ilosci odwiedzin na odpowiedni znak
 
data1 ends
 
;************KOD******************************************************************
 
code1 segment
 
assume cs:code1, ss:stack1, ds:data1    ;dyrektywa zwalniajaca mnie z kazdorazowego podawania segmentu danej
 
start:
   
    mov ax, seg top 		;inicjalizacja stosu
    mov ss, ax
    mov sp, offset top
   
    mov ax, seg data1       ; segment danych do DS
    mov ds, ax
   
    call parseArgs  		;parser argumentow (zjada biale znaki i zapisuje kolejne argumenty w pamieci, oddzielacaj je separatorem)
	
	call checkArgs			;funkcja sprawdzajaca czy zgadza sie ilosc argumentow i ich format
	
	call convertFingerprint	;konwertuje znajdujacy sie w buforze fingerprint, czyli drugi argument, na zapis binarny, ponadto zapisuje w pamieci bit modyfikacji
	
	call fillArray			;wypelnia tablice zgodnie z alogrytmem, bierze pod uwage czy ma nastapic modyfikacja czy nie
	
	call convertArray		;konwertuje ilosc odwiedzin na danym polu na odpowiedni znak
	
	call printArray  		;wyswietla znak, iteruje po wszystkich polach tablicy
   
    exit:					;miejsce skoku, w ktorym program konczy dzialanie
        mov ah,04ch
        int 21h
   
 
; ---------------STALE-------------------------------------------------------------------------------
 
CR equ 0Dh
SPACE equ 20h
TAB equ 09h

; ----------PROCEDURY i makra-------------------------------------------------------------------------
parseArgs proc  		;funckja parsujaca
   
    pusha
	mov ah,51h      	; funkcja przerwania 21 ktora w BX zwraca segment PSP (lini komend)
    int 21h
   
    mov ax, bx
    mov es, ax      	; teraz w ES mam segment PSP
   
    xor cx,cx       	; zeruje CX
   
    mov cl,byte ptr es:[80h]        ; w CL przetrzumuje informacje ile znakow program otrzymal jako argumenty lini polecen
   
    cmp cl,0d
    je parseReturn      		 ; jesli nie podano zadnego argumentu to skocz to konca procedury
   
    mov si,81h    		  ; jesli podano jakies argumenty kontynuuj, ustawiajac SI na piewszy znak argumentow
    mov di, offset Buffer       ; ustawia DI na poczatek docelowej tablicy sparsowanych argumentow
   
    parseArgsLoop:  	;glowna petla parsera
       
        call eatWhiteSpaces ;funkcja polyka spacje i taby, zwraca SI na kolejny element nie bedacy spacja albo tabem (ale moze to byc CR!!!)
       
        xor ax,ax	;zeruje AX
		
		call checkIfCR	;sprawdza czt znnak jest CR
		
		cmp ah, 1d		;jesli CR to wracamy
		je parseReturn
       
        call getArgs    ;jesli nie napotka na CR to wczytuje argumenty
       
        jmp parseArgsLoop   ;kontynuuj petle dopoki sa jeszcze znaki do sparsowania
   
    parseReturn: 			;skok w ktorym wracam z procedury
        popa
		ret
		
parseArgs endp
 
;//////////////////////////////////////////////////////////////////////////////////////////////////////
 
getArgs proc   		 ;procedura zajmujaca sie ladowaniem kolejnych znakow danego argumentu do pamieci
   
    push ax 		;zabezpieczam rejestry AX i BX bo z nich korzystam w tej procedurze
    push bx
   
    xor ch,ch   	;zeruje CH w ktorym trzymam dlugosc kolejnego argumentu(ilosc jego znakow)
   
    copyLoop: 		 ;glowna petla kopiujaca
       
        push ax 	;zabezpieczam AX
       
        mov ah, byte ptr es:[si]    ;dwie instrukcje odpowiedzialne za przekopiowanie niebialego znaku do bufora
        mov byte ptr ds:[di],ah
       
        pop ax
       
        inc ch  	;zwieksz licznik dlugosci danego argumentu
       
        inc si 		;przechodze na kolejny znak
       
        inc di  	;DI rowniez przechodzi na kolejny spot
       
         
        mov al, byte ptr es:[si]    ;jesli napotka na CR to konczy procedure
        cmp al,CR
        je InsertSeparator
       
       
        cmp al,TAB 	;czy napotkany znak jest bialy?
        je InsertSeparator
       
        sub al, SPACE   ;czy napotkany znak jest bialy?
        jz InsertSeparator
       
		jmp copyLoop    ;jesli nie jest spacja ani tabem ani nie CR to musi byc zwyklym znakiem wiec skacze do poczatku kopiowania
           
    InsertSeparator:    ;skok, w ktorym wstawiam separator a nastepnie zwiekszam DI na kolejny spot
       
        mov ah, "$"
        mov byte ptr ds:[di], ah    ;wstawia w buforze seperator dolar pomiedzy kolejnymi argumentami
       
        inc di  		;zwiekszam DI bo cos wstawilem (nie chce potem tego nadpisac)
       
       
        ;fragment ten kopiuje na odpowiednie miejsce w tablicy ArgLengths dlugosc (ilosc znakow) danego argumentu
        push di
        push ax 		;zabezpieczam rejestry ktore uzyje
        xor ax, ax  	;zeruje AX
        mov al, ArgCounter  ;laduje low byte akumulatora wartoscia licznika argumentow
        mov di, offset ArgLengths   ;laduje DI miejscem gdzie zaczyna sie tablica
        add di, ax  	;przesuwam DI na odpowiednie miejsce w tablicy
        mov ds:[di], byte ptr ch    ;zapisuje do tablicy ArgLengths dlugosc danego argumentu
        pop ax  		;odbezpieczam rejestry
        pop di
       
        inc ArgCounter  ;zwieksza licznik argumentow
 
   
    pop bx  			;odbezpieczam AX I BX
    pop ax
    ret
getArgs endp
 
;///////////////////////////////////////////////////////////////////////////////////////////////////////////////
   
eatWhiteSpaces proc 	;procedura ktora polyka kolejny spacje lub taby, zwraca SI na znak nie bedacy spacja ani tabem ale mogacy byc CR
   
    push ax
	
    eatWhiteSpacesLoop:
       
        xor ax,ax
		mov ah, es:[si] ;laduje znak do akumulatora
       
        sub ah, SPACE   ;sprawdzam czy spacja
        jz continueEatWhiteSpaces
		
		mov ah, es:[si] ;laduje znak do akumulatora
       
        sub ah, TAB 	;sprawdzam czy tab, SUB DZZIALA SZYBICIEJ?????????????
        jz continueEatWhiteSpaces
		
	
	pop ax
	ret
    continueEatWhiteSpaces:
       
        inc si 			 ;ide dalej
       
        jmp eatWhiteSpacesLoop
eatWhiteSpaces endp
 
;//////////////////////////////////////////////////////////////////////////////////////////////////

checkIfCR proc			;sprawdza czy nastepny w AL znak to CR, jesli tak zwraca w ah 1

mov al,es:[si]  ;jesli napotka na CR to konczy procedure
cmp al,CR
jne isNotCR
mov ah, 1d
isNotCR:
ret

checkIfCR endp

;/////////////////////////////////////////////////////////////////////////////////////////////////
 
printArgs proc  		;procedura wypisujaca kolejne argumenty jeden pod drugim
 
push ax 				;zabezpieczam rejestry ktore uzywa ta procedura
push dx
push bx
push cx
   
    mov cl, byte ptr ArgCounter ;wczytuje licznik argumentow do wypisania
    mov dx, offset Buffer   ;wczytuje z pamieci tablice ze sparsowanymi argumentami odzielonymi dolarem
    mov bx, offset ArgLengths   ;wczytuje z pamieci tablice z dlugosciami kolejnych argumentow
   
    printArgsLoop:  ;glowna petla, wykona sie tyle razy ile jest wczytanych argumentow
       
       
        ;jesli nie podano argumentu to odrazu przeskocz do konca bo nie ma nic do wyswietlania
        cmp cl,0d
        je noArgsJmp
       
        mov ah,9h   ;wypisz ciag znakow do dolara (czyli jeden argument)
        int 21h
       
        push dx     ;wypisuje znak nowej lini
        mov dx, offset NewLine
        mov ah,9h
        int 21h
        pop dx
       
        xor ax,ax   ;wyzeruj ax
       
        mov al, byte ptr [bx]   ;zapisz w al dlugosc kolejnego argumentu
        add dx,ax   ;przesun o tyle indeks odpowiedzialny za wypisywanie
       
        inc dx  ;zwieksz ten indeks jeszcze o 1, bo trzeba minac dolara
        inc bx  ;przejdz na kolejny element w tablicy dlugosci argumentow
        dec cl  ;zmniejsz licznik pozostalych do wypisania argumentow o 1
   
    cmp cl, 0d  ;jesli zostaly jeszcze jakies argumenty do wypisania do skocz do poczatku petli
    jne printArgsLoop
 
noArgsJmp: 
pop cx  ;odbezpieczam uzyte rejestry
pop bx
pop dx
pop ax
ret
 
printArgs endp

;////////////////////////////////////////////////////////////////////////////////////////////////////////

checkArgs proc

	pusha
	
	;sprawdza czy otrzymal dokladnie dwa argumenty
	mov al, [ArgCounter]
	cmp al, 2d
	jne error1
	
	;sprawdza czy dlugsc flagi modyfikacji wynosi 1
	mov al, [ArgLengths]
	cmp al, 1d
	jne error2
	
	;sprawdza czy flaga modyfikacji to 0 lub 1
	mov al, byte ptr [Buffer]
	cmp al, "0"
	je continueFlagValid
	cmp al, "1"
	je continueFlagValid
	jmp error2
	continueFlagValid:
	
	;sprawdza czy dlugosc drugiego argumentu(skrotu) wynosi 32
	mov al, [ArgLengths+1]
	cmp al, 32d
	jne error3
	
	;sprawdza czy kolejne znaki skrotu to 0-9 lub a-f lub A-F
	xor cx,cx	;zeruje rejestry
	xor ax,ax
	xor si,si
	mov cl, 32d		;bedziemy iterowac po 32 znakach fingerprinta
	mov ax, offset Buffer	;pobierz offset pierwszego bajtu w buforze
	add ax, 2	;dwa bajty dalej, bo pierwszy znak w Bufferze to bit modyfikacji, drugi to separator, trzeci dopiero to poczatek fingerprinta
	mov si, ax
	checkArg2Loop:
		mov al, byte ptr ds:[si]
		
		cmp	al, '0'	;jesli numer mniejszy niz zera to na pewno zly znak
		jb	error4
		
		cmp al, ':'	;jesli numer mniejszy od tego co po dziewiatce a przeszedl poprzedni cmp to na pewno dobry znak, mozna isc dalej
		jb	OkByte
		
		cmp al, 'A'	;jesli numer mnieszy niz A i przeszyly poprzednie porownania to na pewno zly znak
		jb	error4
		
		cmp al, 'G'	;jesli numer mniejszy od tego co po F i przeszly poprzednie porownania to na pewno dobry znak i mozna isc dalej
		jb	OkByte
		
		cmp	al, 'a'	;j.w
		jb	error4
		
		cmp al, 'g'	;j.w.
		jb	OkByte
		
		jmp error4
		
		OkByte:
		inc si	;przejdz na kolejny znak
	loop checkArg2Loop
		
	popa
	ret

	;wyswietla odpowiedni komunikat i konczy program
	error1:
		mov ax, offset WrongArgNumb
		call printString
		jmp exit
		
	error2:
		mov ax, offset WrongArg1
		call printString
		jmp exit
	
	error3:
		mov ax, offset WrongArg2Len
		call printString
		jmp exit
	
	error4:
		mov ax, offset WrongArg2Form
		call printString
		jmp exit
		

checkArgs endp



;/////////////////////////////////////////////////////////////////////////////////////////////////////////

printString proc	;input: DS:AX - poczatek ciagu znakow zakonczy znakiem dolara

	push ax
	push dx
	
	mov dx, ax
	mov ah,9h
	int 21h
	
	pop dx
	pop ax
	ret

printString endp

;////////////////////////////////////////////////////////////////////////////////////////////////////////

convertFingerprint proc		;zmienia fingerprint do postaci binarnej, na koncu rowniez zapisuje bit modyfikacji do pamieci

	pusha
	
	mov si, offset Buffer
	add si, 2			;dwa bajty dalej to pierwszy to bit modyfikacji, drugi to separator, dopiero trzeci to poczatek fingerprinta
	mov di, offset Converted
	xor bx,bx			;zeruje BX
	xor cx,cx			;zeruje CX
	mov cl, 16d			;iterowanie 16 razy po 2 znakach naraz, bo znak heksadecymalny odpowiada 4 bitom, wiec bajt to dwa znaki heksadecymalne
	GoToNextByte:
		mov al, byte ptr ds:[si]	;wczytaj pierwszy znak
		inc si			;przejdz na kolejny znak
		call convertASCII	;zmien go na binarny
		mov bl, al		;zrob miejsce w akumulatorze
		
		shl bl, 4d		;zrob miejsce na kolejna czworke bitow
		xor al, al
		mov al, byte ptr ds:[si]	;wczytaj drugi znak
		inc si			;przejdz na kolejny znak
		
		call convertASCII	;zmien na binarny
		or bl, al		;ustaw na 4 mlodszych bitach binarny, drugi znak
		
		mov byte ptr ds:[di], bl	;zapisz bajt w pamieci
		inc di			;przejdz na kolejny spot, na ktory bedziemy kopiowac
		
		dec cl			;dekrementuj licznik petli
	cmp cl, 0d
	jne GoToNextByte
	
	call getModFlag		;zapisuje w pamieci flage modyfikacji
	
	popa
	ret

convertFingerprint endp

;///////////////////////////////////////////////////////////////////////////////////////////////////////////////

getModFlag proc			;zapisuje bit modyfikacji w pamieci

	push ax
	mov al, ds:[Buffer]	;offset tablicy Buffer to wlanie adres, pod ktorym znajduje sie bajt bitu modyfikacji
	sub al, "0"			;zmienia z kodu ASCII na faktyczna liczbe 0 lub 1 (binarna liczbe)
	mov byte ptr ds:[Modification], al	;zapisuje ten bit w pamieci
	pop ax
	ret

getModFlag endp

;//////////////////////////////////////////////////////////////////////////////////////////////////////////////

convertASCII proc		;input: znak heksadecymalnie w AL(ASCII), output: znak binarnie

	cmp al, "A"	
	jae	letter			;jesli wiekszy niz 9 to na pewno litera
	sub al, 48d			; jesli nie to zmieni cyfre
	jmp returnJump
	
	letter:
	cmp al, "a"
	jae lower			;jesli wiecej to na pewno mala litera
	sub al, 55d			; jesli nie to zmieni duza litere
	jmp returnJump
	
	lower:
	sub al, 87d			; zmieni mala litere
	
	returnJump:
	ret

convertASCII endp

;//////////////////////////////////////////////////////////////////////////////////////////////////////////////

printArray proc			;wypisuje tablice

	pusha
	
	;wypisz gorna ramke
	mov ax, offset TopLine
	call printString
	
	mov bx,offset Array	;zaladuj poczatek tablicy
	mov si, bx
	
	mov cx, 9d			;9 wierszy do wypisania w petli glownej petli
	
	PrintLineLoop:
		mov dl, '|'		;wypisz bok ramki
		call printCharacter		
		push cx			;zabezpiecz CX, zeby mozna zagniezdzic petle
		mov cx, 17d		;17 znakow do wypisania w jednej linii
		PrintFieldLoop:
			mov dl, byte ptr ds:[si]	;wypisz znak
			call printCharacter
			inc si		;i idz dalej
			loop PrintFieldLoop	
		pop cx
		mov dl,'|'		;po wypisaniu lini, wypisz prawy bok rami
		call printCharacter
		mov dl, 10		;i zejdz do kolejnej linii
		call printCharacter
		mov dl, 13
		call printCharacter
		loop PrintLineLoop
	
	;wypisz dolna ramke
	mov ax, offset BottomLine
	call printString

	popa
	ret

printArray endp

;/////////////////////////////////////////////////////////////////////////////////////////////////////////////////

printCharacter proc		;wypisuje znak i przesuwa kursor dalej, INPUT: dl - znak do wypisania

	pushf
	push ax
	
	mov ah,2h
	int 21h
	
	pop ax
	popf
	ret

printCharacter endp

;/////////////////////////////////////////////////////////////////////////////////////////////////////////////////

convertArray proc		;konwertuje ilosc odwiedzin na danym miescu na odpowiedni znak, wpisuje rowniez w odpowiednie miejsce znak startu i konca, INPUT: bx - miejsce, w ktore wykonano ostatni ruch

	push ax
	push dx
	push di
	push si
	push bx 
	
	mov	ax, offset Array
	dec ax				;startuje o jeden mniej bo w petli inkrementuje na poczatku
	mov di, ax	
	mov si, ax
	mov	cx, 153d
	convertLoop:
		xor ax,ax
		xor bx,bx
		
		inc si
		inc di
		
		mov al, byte ptr ds:[si]
		sub al, 0d
		jz NextField	;jesli ani raz nie odwiedzony to idz na nastepny
		
		mov al, byte ptr ds:[si]
		cmp al, 15d
		jae Above14
		mov bl, al		;jesli ilosc odwiedzin <= 14 to wstaw znak odpowiadajacy ilosci odwiedzin
		dec bl 			;zeby zgadzala sie kolejnosc znakow
		mov al, byte ptr ds:[ASCIItable+bx]
		mov byte ptr ds:[di], al	;wstaw znak
		jmp NextField	;idz dalej
		
		Above14:		;jesli ilosc odwiedzin >14 to wstaw "^"
		inc bx	;dalej
		mov al, byte ptr [ASCIItable+13]
		mov byte ptr ds:[di], al		;wstaw znak
		
		NextField:		;przejdz na kolejne miejsce w tablicy
		loop convertLoop	;iteruj po calej tablicy
	
	pop bx				;wroc do starej wartosci BX(czyli miejsce ostatniego skoku)
	mov ds:[Array+bx], byte ptr 69d		;wstaw w miescje ostatniego skoku znak E
	mov ds:[Array+76], byte ptr 83d		;wstaw w miejsce startu znak S
	pop si
	pop di
	pop dx
	pop ax
	ret

convertArray endp

;//////////////////////////////////////////////////////////////////////////////////////////////////////////

fillArray proc			;wypelnia tablicy zgodnie z algorytmem, OUTPUT: bx - pozycja ostatniego miejsca skoku figury w tablicy Array, bierze pod uwage czy ma byc modyfikacja czy nie

	push ax				;zabezpieczam rejestry, ktore uzywam
	push cx
	push dx
	push si
	push di
	
	xor cx,cx			;zeruje rejestry, dla pewnosci
	xor ax,ax
	xor dx,dx
	xor bx,bx
	
	mov si, offset Converted	;pobierz ciag bajtow w postaci binarnej
	mov di, offset Array	;pobierz poczatek tablicy, konieczne do inkrementowania licznika odwiedzin miejsca

	mov bl, 76d			;pozycja startu
	mov cx, 16d			;iterujemy po 16 bajtach skrotu
	ProcessByte:
		mov al, byte ptr ds:[si]	;pobierz bajt
		inc si			;idz dalej
		push cx			;zabezpiecz CX zeby mozna zagniezdzic petle
		mov cx, 4d		;cztery pary bitów w bajcie do przeanalizowania
		ProcessBitPair:
			mov dl, al
			and dl, 00000010b	;zeruje te, ktore w masce sa zerami, te ktore sa jedynkami nie rusza
			cmp dl, 00000010b	;sprawdza czy 2 bit jest ustawiony
			je moveDownJmp		;jesli tak do ruch w dol
			call moveUp			;jesli nie to ruch do gory
			jmp moveUpJmp		;nie chce skakac, tylko uzywac procedur
			moveDownJmp:
			call moveDown
			moveUpJmp:
			
			mov dl, byte ptr ds:[Modification]	;pobierz z pamieci bit modyfikacji
			cmp dl, 0d			;czy jest on rowny zero?
			je MoveOn			;jesli tak, to nie ma byc modyfikacji, czyli idziemy dalej
			
			mov dl, al			;jesli nie jest rowny zero, czyli jest jedynka, to ma byc modyfikacja
			and dl, 00000010b	;modyfikacja polega, na tym ze wykonujemy jeszcze jeden ruch w kierunku pionowym
			cmp dl, 00000010b	;ciag instrukcji identyczny jak powyzej, sluzacy do wykonania ruchu w kierunku pionowym, jedynie zmiana etykiet by uniknac kolizji oznaczen
			je moveDownJmp1
			call moveUp
			jmp moveUpJmp1
			moveDownJmp1:
			call moveDown
			moveUpJmp1:
			
			MoveOn:				;idziemy dalej, czyli sprawdzamy jaki ruch ma byc w kierunku poziomym
			mov dl, al
			and dl, 00000001b	;jesli prawy bit jest ustawiony to ruch w prawo
			cmp dl, 00000001b
			je moveRightJmp
			call moveLeft		;jesli nie jest ustawiony to ruch w lewo
			jmp moveLeftJmp
			moveRightJmp:
			call moveRight
			moveLeftJmp:
			
			shr al,2			;przesun bity o 2 w prawo(pozbywa sie dwoch bitow, ktore analizowal w tej iteracji, na ich miejsce ustawia dwa kolejne)
			
			inc byte ptr ds:[di+bx]		;zwieksz licznik odwiedzin danego miejsca
			
			loop ProcessBitPair		;kontynuuj po wszystkich czterech parach bitow w bajcie
		pop cx					;wroc do starego licznika petli zewnetrznej
		loop ProcessByte		;kontynuuj po wszystkich 16-tu bajtach skrotu
	
	;na koncu w bx siedzi indeks miejsca ostatniego skoku, czyli to co wymaga funkcja printujaca tablice, zeby wyswietlic znak "E"
	
	pop di						;odbezpieczam rejestry, ktore uzywalem
	pop si
	pop dx
	pop cx
	pop ax
	ret

fillArray endp

;////////////////////////////////////////////////////////////////////////////////////////////////////////
;Cztery procedury odpowiedzialne za wykonywanie ruchu do gory, w dol, w prawo lub w lewo
;INPUT: bx - obecna pozycja w tablicy
;OUTPUT: bx - zmieniona (lub nie, jesli nie mozna sie ruszyc w danym kierunku)
;wszystkie procedury sprawdzaja, czy mozna wykonac ruch (bez wyjscia poza tablice)

moveUp proc	;ruch do gory

	push dx
    push ax			;zabezpieczam rejestry, ktore uzywam
    mov dl,17d		;do dl laduje 17, czyli ilosc kolumn w tablicy
    mov ax,bx
	div dl			;dzieli akumulator przez swoj operand, w tym przypadku dl, do AH laduje reszte z dzielenia, do AL laduje calkowitoliczbowy wynik dzielenia
	cmp al, 0d		;czy wynik nie jest zerem?
	jne OkayMoveUp	;jesli jest to jestesmy w pierwszym rzedzie, wiec nie robimy ruchu. jesli nie to robimy skok		
	
	retMoveUp:		;wracamy
	pop ax
	pop dx
	ret
	
	OkayMoveUp:
	sub bx,17d	;;jesli nie to robimy ruch: od obecnej pozycji odejmujemy ilosc kolumn tablicy, co przesuwa gonca, do gory o jedna linijke, dalej w tej samej kolumnie
	jmp retMoveUp

moveUp endp

moveDown proc

	push dx
    push ax			;analogicznie j.w.
    mov dl,17d
    mov ax,bx
	div dl			;analogicznie j.w.
	cmp al, 8d		;czy wynik to nie 8?
	jne OkayMoveDown 	;jesli nie to nie jestesmy w ostatnim rzedzie, wiec wykonujemy ruchu
	
	retMoveDown:
	pop ax
	pop dx
	ret
	
	OkayMoveDown:
	add bx, 17d		;jesli nie to wykonujemy ruch w dol, analgicznie j.w. tylko tym razem dodajemy
	jmp retMoveDown

moveDown endp

moveLeft proc

	push dx
    push ax				;analgicznie j.w.
    mov dl,17d
	mov ax,bx
    div dl				;analgicznie j.w.
	cmp ah, 0d			;czy reszta nie wynosi zero?
	jne OkayMoveLeft		;jesli nie, nie jestemy w pierwszej kolumnie, czyli mozemy wykonac ruchu w lewo
	
	retMoveLeft:		;wracamy
	pop ax
	pop dx
	ret
	
	OkayMoveLeft:
	sub bx, 1d			;jesli nie to wykonujemy ruch w lewo, po prostu od BX odejmujemy 1
	jmp retMoveLeft

moveLeft endp

moveRight proc

	push dx
    push ax				;analgicznie j.w.
    mov dl,17d
    mov ax,bx
	div dl				;analgicznie j.w.
	cmp ah, 16d			;czy reszta nie wynosi 16?
	jne OkayMoveRight		;jesli nie, to nie jestemy w ostatniej kolumnie, czyli wykonujemy ruchu w prawo
	
	retMoveRight:		;wracamy
	pop ax
	pop dx
	ret
	
	OkayMoveRight:
	add bx, 1d			;jesli nie to wykonujemy ruch w prawo, po prostu do BX dodajemy 1
	jmp retMoveRight

moveRight endp
   
code1 ends
 
;*************STOS********************************************************************************************
 
stack1 segment stack
top dw ?
    dw 300 dup(?)	;602 bajtowy stos
stack1 ends
 
end start
 
;*************KONIEC***************************************************************************************
