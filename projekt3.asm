;Patryk Wegrzyn, Asemblery 2017
;Projekt3, Trojkat Sierpinskiego

;.286
.387

CR equ 0Dh
SPACE equ 20h
TAB equ 09h
EOF equ 0FFh

;************************DANE******************************************************************************

data1 segment

	Buffer db 300 dup("$")     			;tablica w ktorej, w ktorej przetrzumuje kolejne argumenty odzielone dolarem
	ArgCounter db 0             		;licznik argumentow dostarczonych do programu
	ArgLengths db 150 dup(0)   			;tablica w ktorej przetrzumuje dlugosci (ilosci znakow) kolejnych argumentow
	NewLine db 10,"$"   				;przejscie do nowej lini
	IternumStr db 300 dup("$")			;argumenty jak stringi
	LenStr db 300 dup ("?")
	Iternum db ?						;argumenty jako liczby binarne
	Len db ?
	AngleDelta dw 60					;kat, zaczynamy od 60 po odrazu policze sobie za pomoca tego delte w radianach
	Angle dw 0
	OneThird dd 0						;zapisuje w pamieci stale ktore policzylem na fpu
	AngPlusPi3 dd 0
	ToRadians dw 180					;potrzebne do zmiany kata na radiany
	Xposition dw 0						;tutaj trzymam wspolrzedna X, zaczynam w lewym dolnym rogu, wiec x = 0 na starcie
	Yposition dw 199					;tutaj trzymam wspolrzedna Y, zaczynam w lewym dolnym rogu, wiec y = 199 na starcie
	Color db 12							;kolor, w jakim bede rysowal
	WrongArgNum db "Blad! Oczekiwano 2 argumentow: licznik iteracji oraz dlugosc jednego ruch.",10,13,"$"
	WrongArgForm db "Blad! Argumentami moga byc wylaczenie liczby w systemie dziesietnym.",10,13,"$"
	ArgTooBig db "Blad! Licznik iteracji moze wynosic maksymalnie 8, powniewaz konczy sie limit pamieci segmentu danych.",10,13,"$"
	Lsystem db 25000 dup("$")			;piersza tablica na napis
	Lsystem2 db "A", 25000 dup("$")		;druga tablica na napis, od niej zaczynam
	Flag db 0							;flaga, ktora mowi mi na ktorej tablicy aktualnie znajduje sie napis
	
data1 ends

;************************KOD*******************************************************************************

code1 segment

assume cs:code1, ss:stack1, ds:data1    ;dyrektywa zwalniajaca mnie z kazdorazowego podawania segmentu danej

start:

	mov ax, seg top 		;inicjalizacja stosu
    mov ss, ax
    mov sp, offset top
   
    mov ax, seg data1       ;segment danych do DS
    mov ds, ax
   
    call parseArgs  		;parser argumentow (zjada biale znaki i zapisuje kolejne argumenty w pamieci, oddzielacaj je separatorem)
	
	call checkArgs			;funkcja sprawdzajaca czy zgadza sie ilosc argumentow i ich format
	
	call convertToInt		;Konwertuje argumenty wczytane jako stringi charow na odpowiednie liczby binarne
	
	call createLSystem2		;procedura ta wytwarza odpowiedni napis dla trojkata Sierpinskiego w l-systemie na podstawie wczytanych parametrow
		
	call prepareFpu			;inicjalizuje fpu i wypelnia stos podstawowymi zmiennymi
	
	call drawSierpinski		;rysuje trojkat na podstawie napisu
	
	exit:
		mov ah,04ch
		int 21h
 
; ----------PROCEDURY i makra-----------------------------------------------------------------------------	

parseArgs proc  		;funckja parsujaca
   
    push ax
	push bx
	push cx
	push dx
	push si
	push di
	
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
        pop di
		pop si
		pop dx
		pop cx
		pop bx
		pop ax
		ret
		
parseArgs endp
 
;/////////////////////////////////////////////////////////////////////////////////////////////////////////////////
 
getArgs proc   		 ;procedura zajmujaca sie ladowaniem kolejnych znakow danego argumentu do pamieci
   
    push ax 		;zabezpieczam rejestry AX i BX bo z nich korzystam w tej procedurze
    push bx
   
    xor ch,ch   	;zeruje CH w ktorym trzymam dlugosc kolejnego argumentu(ilosc jego znakow)
   
    copyLoop: 		 ;glowna petla kopiujaca
       
        push ax 	;zabezpieczam AX
       
        mov ah, byte ptr es:[si]    ;dwie instrukcje odpowiedzialne za przekopiowanie niebialego znaku do bufora
        mov byte ptr ds:[di], ah
       
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

checkIfCR proc			;sprawdza czy nastepny w AL znak to CR, jesli tak zwraca w ah 1

	mov al,es:[si]  ;jesli napotka na CR to konczy procedure
	cmp al,CR
	jne isNotCR
	mov ah, 1d
	isNotCR:
	ret

checkIfCR endp

;//////////////////////////////////////////////////////////////////////////////////////////////////////////

checkArgs proc		;sprawdza poprawnosc wczytanych parametrow

	push ax
	push bx
	push cx
	push dx
	push si
	push di
	
	mov al, byte ptr ds:[ArgCounter]
	cmp al, 2d								;sprawdza czy sa 2 argumenty
	jne error1
	
	mov cx,1d
	mov di, offset IternumStr					;kopiuje do pamieci 1szy argument
	call copyArg
	
	mov cx, 2d								;kopiuje do pamieci 2gi argument
	mov di, offset LenStr
	call copyArg
	
	mov si, offset IternumStr
	xor cx,cx
	mov cl, byte ptr ds:[ArgLengths]		;pobieram do licznika dlugosc pierwszego argumentu bo bede iterowal po jego znakach
	checkFstArg:
		mov al, byte ptr ds:[si]			;znak jest cyfra tylko gdy jest z przedzialu [48,57]
		cmp al, 48d
		jb error2
		cmp al, 57d
		ja error2
		inc si
		loop checkFstArg
		
	mov si, offset LenStr
	xor cx,cx
	mov cl, byte ptr ds:[ArgLengths+1]
	checkSndArg:							;analogicznie dla drugiego argumentu
		mov al, byte ptr ds:[si]
		cmp al, 48d
		jb error2
		cmp al, 57d
		ja error2
		inc si
		loop checkSndArg
		
	pop di
	pop si
	pop dx
	pop cx
	pop bx
	pop ax
	ret	
	
	error1:									;wypisz stoswne informacje o bledach i wyjdz z programu
		mov ax, offset WrongArgNum
		call printString
		jmp exit
	
	error2:
		mov ax, offset WrongArgForm
		call printString
		jmp exit
			
checkArgs endp


;///////////////////////////////////////////////////////////////////////////////////////////////////////////
;kopiuje dany argument z bufora do miejsca w pamieci
;input: cx - numer argumentu do skopiwania, numerowanie od 1
;ds:di - offset miejsca docelowego do skopiowania

copyArg proc 
	
	push ax
	push si
	mov si, offset Buffer
	
	skipArgs:
		dec cx
		cmp cx, 0d
		je CopyingLoop
		skipChars:
			mov al, byte ptr ds:[si]
			inc si
			cmp al, "$"
			je skipArgs
			jmp skipChars
			
	CopyingLoop:
		mov al, byte ptr ds:[si]
		cmp al, "$"
		je copyRet
		mov byte ptr ds:[di], al
		inc si
		inc di
		jmp CopyingLoop
		
	copyRet:
		pop si
		pop ax
		ret
copyArg endp

;////////////////////////////////////////////////////////////////////////////////////////////////////////////
;Konwertuje argumenty wczytane jako stringi charow na odpowiednie liczby binarne
;UWAGA: argumenty musza byc dodatnimi liczba calkowitym dziesietnymi z przedzialu 0 do 2^8 !!!

convertToInt proc

	push ax
	push bx
	push cx
	push dx
	push si
	push di
	
	xor ax,ax
	xor bx,bx
	xor cx,cx
	xor dx,dx
	
	mov cl, byte ptr ds:[ArgLengths]		;pobierz dlugosc pierwszego argumentu i zmniejsz ja o 1
	dec cl
	mov si, offset IternumStr				;pobierz adresu pierwszego stringa
	mov ax, 1d
	mov bl, 10d
	
	makeFstBase:							;petla ta tworzy nam 'wage' przez ktora bede mnozyl wartosci odpowiednich znakow ASCII
		cmp cl, 0d
		je skip1
		mul bl
		dec cl
		jmp makeFstBase
	
	skip1:
	xor bx,bx
	mov cl, byte ptr ds:[ArgLengths]
	
	convFstArg:								;petla pobiera kolejne znaki ze stringa, mnozy je przez odpowiednia potege 10 i na koncu sumuje wszystko
		mov dl, byte ptr ds:[si]
		sub dl, 48d							;zamien znak na jego binarny odpowiednik
		inc si
		push ax
		mul dl
		add bx, ax
		pop ax
		push bx
		xor bx,bx
		mov bl, 10d
		div bl
		pop bx
		loop convFstArg
		
	mov ds:[Iternum], byte ptr bl			;zapisz binarny argument do pamieci
	cmp bl, 8								;jesli licznik iteracji jest wiekszy od 8 to zwroc blad, 8 zejsc rekurencyjnych to juz 10kB ciag znakow, a poza tym i tak nie widac roznicy
	ja error3
	cmp bl, 0d								;jesli zero iteracji to odrazu wyjdz z programu
	je exit
	
	xor ax,ax
	xor bx,bx
	xor cx,cx
	xor dx,dx
	
	mov cl, byte ptr ds:[ArgLengths+1]		;analogiczny zestaw instrukcji tylko dla drugiego argumentu
	dec cl
	mov si, offset LenStr
	mov ax, 1d
	mov bl, 10d
	
	makeSndBase:
		cmp cl, 0d
		je skip2
		mul bl
		dec cl
		jmp makeSndBase
	
	skip2:
	xor bx,bx
	mov cl, byte ptr ds:[ArgLengths+1]
	
	convSndArg:
		mov dl, byte ptr ds:[si]
		sub dl, 48d
		inc si
		push ax
		mul dl
		add bx, ax
		pop ax
		push bx
		xor bx,bx
		mov bl, 10d
		div bl
		pop bx
		loop convSndArg
		
	mov ds:[Len], byte ptr bl

	pop di
	pop si
	pop dx
	pop cx
	pop bx
	pop ax
	ret
	
	error3:
		mov ax, offset ArgTooBig
		call printString
		jmp exit

convertToInt endp

;//////////////////////////////////////////////////////////////////////////////////////////////////////////////
;procedura ta wytwarza odpowiedni napis dla trojkata Sierpinskiego w l-systemie na podstawie wczytanych parametrow
;zlozonosc O(n^3, gdzie n to ilosc znakow w napisie :( dlatego ogarniczenie dla max 7 iteracji, bo dla 8 juz trwa za dlugo, poza tym dla 8 trojkat i tak juz wyglada tak samo bo nie miesci sie na ekranie

; createLSystem proc

	; push ax
	; push bx
	; push cx
	; push dx
	; push si
	; push di
	
	; xor cx,cx
	; mov cl, byte ptr ds:[Iternum]			;pobierz licznik iteracji
	
	; LSysLoop:								;glowna petla funkcji
		
		; mov si, offset Lsystem				;zacznij przetwarzac ciag od poczatku
		; mov di,si
		
		; LSysIter:							;petla ta przechodzi po wszystkich znakach ciagu
			; mov al, byte ptr ds:[si]
			
			; cmp al, "$"						;jesli dolar to koniec ciagu i wracamy
			; je exitInnerLoop
			
			; cmp al, "+"						;pomin ten znak
			; je continueInnerLoop
			
			; cmp al, "-"						;ten rowniez
			; je continueInnerLoop
			
			; cmp al, "A"						;jesli nie A to B wiec skocz do przetwarzania B
			; jne skipToB
			
			; push cx							;zapamietaj rejestry bo zaraz wchodzisz do kolejnej petli
			; push si
			; push di
			; mov cx, 4d						;cztery razy przesun ciag znakow o 1

			; pushChars:
				; inc si
				; inc di
				; push si
				; push di
				; pushByOne:					;ta petla przepycha kolejne litery az dopoki nie napotka na dolara
					; mov bl, al
					; mov al, byte ptr ds:[si]
					; mov byte ptr ds:[di], bl
					; cmp al, "$"
					; je pushedByOne
					; inc si
					; inc di
					; jmp pushByOne
				
				; pushedByOne:
				; pop di
				; pop si
				; loop pushChars
			; pop di
			; pop si
			; pop cx
			
			; mov ds:[di], byte ptr "B"		;wstaw odpowiedni ciag w zrobione przed chwila miejsce
			; inc di
			; mov ds:[di], byte ptr "-"
			; inc di
			; mov ds:[di], byte ptr "A"
			; inc di
			; mov ds:[di], byte ptr "-"
			; inc di
			; mov ds:[di], byte ptr "B"
			; add si, 4d
			
			; jmp continueInnerLoop			;skoro przetworzyles A to pomin B i kontynuuj droga po kolejnych znakach
			
			; LSysLoopHalf:					;etykieta skoku posredniego, bo jeden dlugi jest za zdecydowanie za dlugi
				; jmp LSysLoop
			
			; skipToB:						;analogiczna sekwencja instrukcji dla znaku B
			; push cx
			; push si
			; push di
			; mov cx, 4d

			; pushChars2:
				; inc si
				; inc di
				; push si
				; push di
				; pushByOne2:
					; mov bl, al
					; mov al, byte ptr ds:[si]
					; mov byte ptr ds:[di], bl
					; cmp al, "$"
					; je pushedByOne2
					; inc si
					; inc di
					; jmp pushByOne2
				
				; pushedByOne2:
				; pop di
				; pop si
				; loop pushChars2
			; pop di
			; pop si
			; pop cx
			
			; mov ds:[di], byte ptr "A"
			; inc di
			; mov ds:[di], byte ptr "+"
			; inc di
			; mov ds:[di], byte ptr "B"
			; inc di
			; mov ds:[di], byte ptr "+"
			; inc di
			; mov ds:[di], byte ptr "A"
			; add si, 4d
			
			; continueInnerLoop:				;idz do kolejnego znaku
			; inc si
			; inc di
			; jmp LSysIter
		
		; exitInnerLoop:	
		; dec cl
		; cmp cl, 0d
		; je outOfLoop
		; jmp LSysLoopHalf
	
	; ;+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
	; ;Nie jestem pewny czy poniszy fragment jest konieczy,
	; ;jest on tylko po to zeby odrocic + na - i vice versa gdy licznik iteracji jest nieparzysty
	; ;Po to, zeby trojkat zawsze "rosl w gore", bez tego rosnie na przemian w gore i w dol
	; ;+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
	
	; outOfLoop:
	; xor ax,ax
	; mov al, byte ptr ds:[Iternum]
	; xor bx,bx
	; mov bx, 1d
	; and bx,ax
	; cmp bx, 0d
	; je DontReverse
	
	; mov si, offset Lsystem
	; dec si
	; mov di,si
	
	; Reverse:
		
		; inc si
		; inc di
		; mov al, byte ptr ds:[si]
		; cmp al, "$"
		; je DontReverse
		; cmp al, "+"
		; je ChangeToMinus
		; cmp al, "-"
		; je ChangeToPlus
		; jmp Reverse
		
		; ChangeToPlus:
		; mov al,"+"
		; mov byte ptr ds:[di],al
		; jmp Reverse
		
		; ChangeToMinus:
		; mov al, "-"
		; mov byte ptr ds:[di],al
		; jmp Reverse
		
	; DontReverse:
	; pop di
	; pop si
	; pop dx
	; pop cx
	; pop bx
	; pop ax
	; ret

; createLSystem endp

;///////////////////////////////////////////////////////////////////////////////////////////////////////////
;glowna procedura odpowiedzialna za rysowanie trojkata Sierpinskiego na podstawie stworzonego napisu

drawSierpinski proc

	push ax
	push bx
	push cx
	push dx
	push si
	push di
	push es
	
	mov ax, 13h								;uruchamia tryb graficzny 320x200 256 kolorow
	int 10h
	mov ax, 0A000h
	mov es, ax								;w ES mam teraz adres segmentu karty graficznej
	
	mov al, byte ptr ds:[Flag]				;jesli flaga jest ustawiona to przypadek nieparzysty
	cmp al, 0d
	je CaseOne
	
	mov si, offset Lsystem
	jmp MainDrawLoop
	
	CaseOne:
	mov si, offset Lsystem2					;pobierz offset napisu
	
	MainDrawLoop:							;glowna petla, ktora idize po wszystkich znakach
		mov al, byte ptr ds:[si]			;pobierz znak
		inc si								;przejdz na kolejny znak
		
		cmp al, "$"							;jesli to dolar to skoncz rysowac
		je StopDrawing
		
		cmp al, "+"							;jesli to + to obort przeciwnie to wskazowek zegara
		je JrotateLeft
		
		cmp al, "-"							;jesli to - to obrot zgodnie ze wskazowkami zegara
		je JrotateRight
		
		call drawLine						;jesli nie dolar ani minus ani plus to napewno A albo B wiec rysuj linie
		jmp MainDrawLoop
		
		JrotateLeft:						;rotacja w lewo
		fxch st(2)							;0:kat 1:y 2:x 3:pi/3
		fsub st(0),st(3)					;0:zmieiony kat 1:y 2:x 3:pi/3
		fxch st(2)							;0:x 1:y 2:kat 3:pi/3
		jmp MainDrawLoop					;kontynuowanie petli po znkach
		
		JrotateRight:						;rotacja w prawo
		fxch st(2)							;0:kat 1:y 2:x 3:pi/3
		fadd st(0), st(3)					;0:zmieniony kat 1:y 2:x 3:pi/3
		fxch st(2)							;0:x 1:y 2:kat 3:pi/3
		jmp MainDrawLoop					;kontynuowanie petli po znkach
		
	StopDrawing:							;oczekiwanie na wcisniecie ESC
	in al,60h
	cmp al,1d
	jne StopDrawing
	mov ax,3								;powrot do trybu tekstowego
	int 10h
	
	pop es
	pop di
	pop si
	pop dx
	pop cx
	pop bx
	pop ax
	ret

drawSierpinski endp

;////////////////////////////////////////////////////////////////////////////////////////////////////////////
;rysuje linie o dlugosci len w kierunku obecnie ustawionym
; 0:x
; 1:y
; 2:kat
; 3:pi/3

drawLine proc
	
	push ax
	push di
	
	fld st(2)					;0:kat 1:x 2:y 3:kat 4:pi/3
	fsincos						;0:cos 1:sin 2:x 3:y 4:kat 5:pi/3
	push cx						;zabezpiecz cx
	xor cx, cx					;wyczysc cx
	fxch st(3)					;0:y 1:sin 2:x 3:cos 4:kat 5:pi/3
	fxch st(1)					;0:sin 1:y 2:x 3:cos 4:kat 5:pi/3
	fxch st(2)					;0:x 1:y 2:sin 3:cos 4:kat 5:pi/3
	mov cl, byte ptr ds:[Len]
	
	LineLoop:
		push cx					;zapamietaj cx, ile pixeli do narysowania jeszcze
		call drawPoint			;narysuj punkt w tym miejscu
		fadd st(0),st(3)		;x = x + 1*cos(kat)
		fxch st(1)				;0:y 1:x 2:sin 3:cos 4:kat 5:pi/3
		fadd st(0),st(2)		;y = y + 1*sin(kat)
		pop cx					;wroc z starym cx
		fxch st(1)				;0:x 1:y 2:sin 3:cos 4:kat 5:pi/3
		loop LineLoop			;wykonaj to len razy
	
	fxch st(2)					;0:sin 1:y 2:x 3:cos 4:kat 5:pi/3
	faddp st(0),st(0)			;0:y 1:x 2:cos 3:kat 4:pi/3
	fxch st(2)					;0:cos 1:x 2:y 3:kat 4:pi/3
	faddp st(0),st(0)			;0:x 1:y 2:kat 3:pi/3
	
	pop cx
	pop di
	pop ax
	ret

drawLine endp

;////////////////////////////////////////////////////////////////////////////////////////////////
;rysuje punkt w odpowiednim miejscu na ekranie
;rysowanie nie opiera sie na korzystaniu z przerwania poniewaz jest to bardzo powolne
;opiera sie ono na ladowaniu odpowiednich komorek pamieci odpowiednim kolorem
;przyspieszylem to stosujac tutaj przesuniecia bitowe zamiast powolnego mnozenia
;Wymaga zeby w ES siedzial adres segmentu karty graficznej

drawPoint proc

	push ax
	push di
	
	
	fld st(0)						;zrob kopie xposition na wierzcholku
	frndint							;zaokraglij ta kopie do intu, wedlug stanu rejestru slowa kontrolnego
	fist word ptr Xposition			;zapisz teraz tego inta do pamieci
	faddp st(0),st(0)				;usun kopie
	fxch st(1)						;zamien miejscami x i y
	fld st(0)						;zrob kopie yposition na wierzcholku
	frndint							;zaokraglij ta kopie do intu, wedlug stanu rejestru slowa kontrolnego
	fist word ptr Yposition			;zapisz teraz tego inta do pamieci
	faddp st(0),st(0)				;usun kopie
	fxch st(1)						;powrot do stanu sprzed funkcji
	
	mov ax, word ptr ds:[Yposition]	;pobierz wspolrzedna Y
	cmp ax, 199
	ja OutOfScreen
	mov di, ax						;zrob kopie Y w di
	mov cl,6d
	shl ax,cl						;AX = AX*64 = 64y
	mov cl,8d
	shl di,cl						;DI = DI*256 = 256y				
	add di,ax						;DI = 64y + 256y = 320y
	mov cx, word ptr ds:[Xposition]
	cmp cx, 319
	ja OutOfScreen
	add di, cx						;DI = 320y + x
	
	;cmp di, 64000d					;jesli wyjdzie poza ekran to nie rysuj
	;ja OutOfScreen
	
	mov al, byte ptr ds:[Color]		;pobiera kolor pixela
	mov byte ptr es:[di], al		;zapisuje kolor w VGA
	
	OutOfScreen:
	pop di
	pop ax
	ret

drawPoint endp

;////////////////////////////////////////////////////////////////////////////////////////////////////////////
;inicjalizuje dobiera odpowiedni kat poczatkowy,
;inicjalizuje FPU, laduje na stos FPU odpowiednie wartosci poczatkowe
; FPUstack po powrtocie z tej funkcji:
; 0:x
; 1:y
; 2:kat
; 3:pi/3

prepareFpu proc

	push ax
	push dx
	
	; xor ax,ax
	; mov al, byte ptr ds:[Iternum]
	; mov dl, 2d
	; div dl
	; cmp ah, 0d
	; je EvenIter
	
	; mov ax, 60d
	; mov word ptr ds:[Angle], ax
	; jmp SkipEvenIter
	
	; EvenIter:
	; xor ax,ax
	; mov word ptr ds:[Angle], ax
	
	; SkipEvenIter:
	
	
	finit								;inicjalizacja FPU
	fild word ptr AngleDelta			;st0=60
	fild word ptr ToRadians				;st0=180, st1=60
	fdivp st(1),st(0)					;st0=de1/3
	fst OneThird						;zapisz 1/3 do pamieci
	fldpi								;st0=pi, st1=1/3
	fmulp st(1),st(0)					;st0=pi/3
	fild word ptr Angle					;st0=kat, st1=pi/3
	fadd st(0),st(1) 					;st0=kat + pi/3 st1=pi/3
	fstp AngPlusPi3						;zapisz do pamieci
	fild word ptr Angle					;st0=kat st1=pi/3
	fild word ptr Yposition				;st0=y st1=kat st2=pi/3
	fild word ptr Xposition				;st0=x st1=y st2=kat st3=pi/3
	
	pop dx
	pop ax
	ret
	
prepareFpu endp

;////////////////////////////////////////////////////////////////////////////////////////////////////////////

;procedura ta wytwarza odpowiedni napis dla trojkata Sierpinskiego w l-systemie na podstawie wczytanych parametrow

createLSystem2 proc

	push ax
	push bx
	push cx
	push si
	push di
	
	xor cx,cx
	mov cl, byte ptr ds:[Iternum]			;pobierz licznik iteracji
	SierpLoop:
		mov al, byte ptr ds:[Flag]			;pobierz flage
		cmp al, 0d							;jesli zero to przypadek parzysty
		je SecondCase
		
		mov si, offset Lsystem				;jesli nie zero, to przypdaek nieparzysty
		mov di, offset Lsystem2
		mov byte ptr ds:[Flag], 0d
		jmp InsideLoop
		
		SecondCase:
		mov si, offset Lsystem2
		mov di, offset Lsystem
		mov byte ptr ds:[Flag], 1d
		
		InsideLoop:							;iteruje po kolejnych znakach w jednej tablicy
			mov al, byte ptr ds:[si]
			inc si
			
			cmp al, "$"						;jesli dolar to koniec ciagu i wracamy
			je exitLoop
			
			cmp al, "+"						;kopiuj plusa
			je CopyPlus
			
			cmp al, "-"						;kopiuj minusa
			je CopyMinus
			
			cmp al, "A"						;jesli nie A to B wiec skocz do przetwarzania B
			jne skipToB
			
			mov ds:[di], byte ptr "B"
			inc di
			mov ds:[di], byte ptr "-"
			inc di
			mov ds:[di], byte ptr "A"
			inc di
			mov ds:[di], byte ptr "-"
			inc di
			mov ds:[di], byte ptr "B"
			inc di
			jmp InsideLoop
			
			CopyPlus:
			mov byte ptr ds:[di], "+"
			inc di
			jmp InsideLoop
			
			CopyMinus:
			mov byte ptr ds:[di], "-"
			inc di
			jmp InsideLoop
			
			skipToB:
			mov ds:[di], byte ptr "A"
			inc di
			mov ds:[di], byte ptr "+"
			inc di
			mov ds:[di], byte ptr "B"
			inc di
			mov ds:[di], byte ptr "+"
			inc di
			mov ds:[di], byte ptr "A"
			inc di
			jmp InsideLoop
		
		exitLoop:
		loop SierpLoop
		
	;+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
	;Nie jestem pewny czy ponizszy fragment jest konieczy,
	;jest on tylko po to zeby odrocic + na - i vice versa gdy licznik iteracji jest nieparzysty
	;Po to, zeby trojkat zawsze "rosl w gore", bez tego rosnie na przemian w gore i w dol
	;+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
	
	xor ax,ax
	mov al, byte ptr ds:[Flag]
	cmp al, 0d
	je DontReverse
	
	
	mov si, offset Lsystem
	dec si
	mov di,si
	
	Reverse:
		
		inc si
		inc di
		mov al, byte ptr ds:[si]
		cmp al, "$"
		je DontReverse
		cmp al, "+"
		je ChangeToMinus
		cmp al, "-"
		je ChangeToPlus
		jmp Reverse
		
		ChangeToPlus:
		mov al,"+"
		mov byte ptr ds:[di],al
		jmp Reverse
		
		ChangeToMinus:
		mov al, "-"
		mov byte ptr ds:[di],al
		jmp Reverse
		
	DontReverse:
	pop di
	pop si
	pop cx
	pop bx
	pop ax
	ret

createLSystem2 endp

;///////////////////////////////////////////////////////////////////////////////////////////////////////////////

code1 ends

;************************STOS*******************************************************************************

stack1 segment stack
top dw ?
    dw 300 dup(?)	;602 bajtowy stos
stack1 ends

end start

;************************KONIEC******************************************************************************