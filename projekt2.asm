;Patryk Wegrzyn, Asemblery 2017
;Projekt2, Operacje na plikach, CRC16

.286

CR equ 0Dh
SPACE equ 20h
TAB equ 09h
BUFSIZE equ 300d	;rozmiar bufora funkcji getchar
EOF equ 0FFh

;************************DANE******************************************************************************

data1 segment

	Buffer db 300 dup("$")      ; tablica w ktorej, w ktorej przetrzumuje kolejne argumenty odzielone dolarem
	ArgCounter db 0             ; licznik argumentow dostarczonych do programu
	ArgLengths db 150 dup(0)    ; tablica w ktorej przetrzumuje dlugosci (ilosci znakow) kolejnych argumentow
	Testing db ?
	NewLine db 10,"$"   		;przejscie do nowej lini
	FormatError db "Blad! Oczekiwano 2 argumenty i potencjalna flage modyfikacji.",10,13,"$"
	SecOptError db "Blad! Niedopuszczalna flaga modyfikacji. Oczekiwano -v.",10,13,"$"
	WrongFirstIn db "Blad! Pierwszy podany plik nie istnieje.",10,13,"$"
	WrongSecIn db "Blad! Drugi podany plik nie istnieje.",10,13,"$"
	ErrorOpening1 db "Wystapil nieoczekiwany blad przy otwieraniu pierwszego pliku wejsciowego.",10,13,"$"
	ErrorOpening2 db "Wystapil nieoczekiwany blad przy otwieraniu drugiego pliku wejsciowego.",10,13,"$"
	ErrorOpening3 db "Wystapil nieoczekiwany blad przy otwieraniu pliku wyjsciowego.",10,13,"$"
	ErrorClosingInput1 db "Wystapil nieoczekiwany blad przy zamykaniu pierwszego pliku wejsciowego.",10,13,"$"
	ErrorClosingInput2 db "Wystapil nieoczekiwany blad przy zamykaniu drugiego pliku wejsciowego.",10,13,"$"
	ErrorClosingOutput db "Wystapil nieoczekiwany blad przy zamykaniu pliku wyjsciowego",10,13,"$"
	ErrorCreatingOutput db "Wystapil nieoczekiwany blad przy tworzeniu pliku wyjsciowego.",10,13,"$"
	ErrorReadingFile db "Wystapil nieoczekiwany blad przy wczytywaniu danych z pliku wejsciowego.",10,13,"$"
	WrongCRC db "Wystapil blad w formacie kodu CRC znajdujacego sie w drugim pliku wejsciowym.",10,13,"$"
	DifferentCRC db "Wyznaczona suma kontrolna CRC16 pierwszego pliku wejsciowego rozni sie od sumy kontrolnej CRC16 wykrytej w drugim pliku wejsciowym.",10,13,"$"
	SameCRC db "Wyznaczona suma kontrolna CRC16 pierwszego pliku wejsciowego jest identyczna do sumy kontrolnej CRC16 wykrytej w drugim pliku wejsciowym.",10,13,"$"
	ErrorSaveCRC db "Wystapil nieoczekiwany blad podczas proby zapisu kodu CRC16 do pliku wyjsciowego.",10,13,"$"
	SavingSucces db "Kod CRC16 wygenerowany i zapisany poprawnie.",10,13,"$"
	FirstInput db 300 dup(0)	;nazwa pierwszego pliku wejsciowego
	SecondInput db 300 dup(0)	;nazwa drugiego pliku wejsciowego
	Output db 300 dup(0)		;nazwa pliku wyjsciowego
	Modification db ? 			;jesli jest ustawiona na 1 to drugi przypadek programu, jesli 0 to pierwszy
	HandleIn1 dw ?				;uchwyty do plikow
	HandleIn2 dw ?
	HandleOut dw ?
	GetCharBuffer db BUFSIZE dup(0),0,0,0	;bufora na wczytywane znaki
	BytesInBuf dw 0				;ilosc znakow znajdujacych sie obecnie w buforze getchara
	Position dw 0				;ktory bajt pliku jest obecnie przetwarzany
	CRC1 dw 0					;pierwszy kod CRC
	CRC2 dw 0 					;drugi kod CRC
	Polynomial dw 0A001h		;reversowany 8005, bo robie metode bit by bit reflected
	CRC1String db 0,0,0,0,0		;cztery bajty na crc do wypisania zakonczone zerem

data1 ends

;************************KOD*******************************************************************************

code1 segment

assume cs:code1, ss:stack1, ds:data1    ;dyrektywa zwalniajaca mnie z kazdorazowego podawania segmentu danej

start:

	mov ax, seg top 		;inicjalizacja stosu
    mov ss, ax
    mov sp, offset top
   
    mov ax, seg data1       ; segment danych do DS
    mov ds, ax
   
    call parseArgs  		;parser argumentow (zjada biale znaki i zapisuje kolejne argumenty w pamieci, oddzielacaj je separatorem)
	
	call checkArgs			;funkcja sprawdzajaca czy zgadza sie ilosc argumentow i ich format, zapisuje w pamieci nazwy plikow wejsciowych, o ile istnieja, i nazwy pliku wyjsciowego
	
	call initiateFiles      ;otwiera odopowiednie pliki(jesli dojdzie do bledu to informuje i konczy program), zapamietuje uchwyty do plikow, tworzy output file jesli nie istnieje
	
	call getCRC16			;tworzy i zapisuje do pamieci kod CRC pierwszego pliku wejsciowego
	
	call changeMode			;wykrywa czy flaga modyfikacji -v byla uruchomiona i w zaleznosci od tego dalej kieruje przebiegiem programu
	
	call checkCRC16			;jesli flaga modyfikacji jest ustawiona to obsluz drugi przypadek czyli porownanie zgodnosci CRC i skocz do konca programu
	
	saveCRCjmp:
		call saveCRC16

	exitCloseFiles:					;miejsce skoku, w ktorym program konczy dzialanie
		call closeFiles			;zamyka pliki
    
	exitNormal:
		mov ah,04ch
		int 21h
 
; ----------PROCEDURY i makra-----------------------------------------------------------------------------	

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

checkArgs proc		;sprawdza poprawnosc wczytanych parametrow, zapisuje nazwy podanych plikow wejsciowychw w pamieci, o ile istnieja

	pusha
	
	mov al, [ArgCounter]	;sprawdza ilosc wczytanych parametrow
	cmp al, 2d
	je FirstCase
	cmp al, 3d		;jesli 3 to trzeba jeszcze sprawdzic poprawnosc flagi modyfikacji
	je SecondCase
	jmp error1		;w kazdym innym razie zwroc blad
	
	FirstCase:
		xor al,al		;ustaw flage modyfikacji programu na 0
		mov byte ptr ds:[Modification], al
		
		mov di, offset FirstInput
		mov cx, 1d
		call copyArg		;kopiuje pierwszy input do pamieci
		mov dx, offset FirstInput
		call checkIfExists
		cmp al, 0d
		je error3			;jesli nie istnieje zwroc blad
		
		mov di, offset Output	;jesli istnieje to zanim wrocisz, zapisz nazwe outputu do pamieci
		mov cx, 2d
		call copyArg
		jmp argsOk
	
	SecondCase:
		mov al, 1d		;ustaw flage modyfikacji na 1
		mov byte ptr ds:[Modification], al
		
		mov al, byte ptr [Buffer]	;czy pierwszy bajt to znak pauzy
		cmp al, "-"
		je continueChecking		;jesli tak to sprawdzaj dalej
		jmp error2
	
		continueChecking:			;czy drugi bajt bufora to znak v
		mov al, byte ptr [Buffer+1]
		cmp al, "v"
		jne error2		;jesli nie to zwroc blad
		
		mov di, offset FirstInput
		mov cx, 2d
		call copyArg		;zapisuje pierwszy input w pamieci
		mov dx, offset FirstInput
		call checkIfExists	;sprawdza czy istnieje
		cmp al, 0d
		je error3
		
		mov di, offset SecondInput	;zapisuje drugi input w pamieci
		mov cx, 3d
		call copyArg
		mov dx, offset SecondInput
		call checkIfExists		;sprawdza czy istnieje
		cmp al, 0d
		je error4
		
		jmp argsOk		;jesli tak to zwroc OK
		
	error1:			;blady do wypisania
		mov ax, offset FormatError
		call printString
		jmp exitNormal
		
	error2:
		mov ax, offset SecOptError
		call printString
		jmp exitNormal
		
	error3:
		mov ax, offset WrongFirstIn
		call printString
		jmp exitNormal
	
	error4:
		mov ax, offset WrongSecIn
		call printString
		jmp exitNormal

	argsOk:		
	popa
	ret
	
checkArgs endp


;///////////////////////////////////////////////////////////////////////////////////////////////////////////
;kopiuje dany argument z bufora do miejsca w pamieci
;input: cx - numer argumentu do skopiwania, numerowanie od 1
;		ds:di - offset miejsca docelowego do skopiowania
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
;spradza czy plik istnieje 
;in: ds:dx - nazwa pliku zakonczona 0
;out: al - 0 plik nie istnieje, al - 1 plik istnieje

checkIfExists proc

	push cx
	mov cx, 3Fh ;dowolny plik
	mov ah, 4Eh	;funkcja przerwania 21 ktora zwraca pierwszy spotkany plik o danej nazwe
	int 21h
	jc DoesntExist	;jesli carry flag jest ustawiony to funkcja zwrocila blad
	mov al, 1d
	pop cx
	ret
	DoesntExist:
		xor al,al
		pop cx
		ret

checkIfExists endp

;//////////////////////////////////////////////////////////////////////////////////////////////////////////////
;otwiera odopowiednie pliki(jesli dojdzie do bledu to informuje i konczy program), zapamietuje uchwyty do plikow, tworzy output file jesli nie istnieje

initiateFiles proc
	
	pusha
	
	mov ah, 3Dh		;otworz pierwszy input w trybie do odczytu
	mov al, 0d
	mov dx, offset FirstInput
	int 21h
	jc errorFile1	;jesli cf jest ustawiony to doszlo do bledu przy otwieraniu
	mov word ptr ds:[HandleIn1], ax	;jesli ok to zapamietuje handle
	
	mov al, byte ptr ds:[Modification]		;jesli flaga modyfikacji nie jest ustawiona to przejdz od obslugi przypadku pierwsszego
	cmp al, 1d
	je SecondCase2
	
	mov dx, offset Output		;jesli flaga nie ustawiona to przypadek pierwszy, zaczynam od sprawdzenia czy output juz istnieje
	call checkIfExists
	cmp al, 0d
	je createOutput		;jesli nie istnieje to stworz go
	
	mov ah, 3Dh		;otworz pierwszy output w trybie do zapisu
	mov al, 1d
	mov dx, offset Output
	int 21h
	jc errorFile3	;jesli cf jest ustawiony to doszlo do bledu przy otwieraniu
	mov word ptr ds:[HandleOut], ax	;jesli ok to zapamietuje handle
	jmp InitiatingSucces
	
	createOutput:
		mov ah, 3Ch		;funkcja przerwania 21h ktora tworzy plik
		mov cx, 0d		;cx = 0 wiec nie nadajemy plikowi zadnych specjalnych atrybutow
		mov dx, offset Output
		int 21h
		jc errorOutput	;jesli cf ustawiony to obsluguje blad
		mov word ptr ds:[HandleOut], ax	;jesli nie to zapamietuje uchwyt
		jmp InitiatingSucces
		
	
	SecondCase2:		;flaga ustawiona wiec obsluz drugi przypadek
		mov ah, 3Dh		;otworz drugi input w trybie do odczytu
		mov al, 0d
		mov dx, offset SecondInput
		int 21h
		jc errorFile2	;jesli cf jest ustawiony to doszlo do bledu przy otwieraniu
		mov word ptr ds:[HandleIn2], ax	;jesli ok to zapamietuje handle
		jmp InitiatingSucces
		
	
	errorFile1:
		mov ax, offset ErrorOpening1
		call printString
		jmp exitNormal
	
	errorFile2:
		mov ax, offset ErrorOpening2
		call printString
		jmp exitNormal
	
	errorFile3:
		mov ax, offset ErrorOpening3
		call printString
		jmp exitNormal
	
	errorOutput:
		mov ax, offset ErrorCreatingOutput
		call printString
		jmp exitNormal
		
	InitiatingSucces:
		popa
		ret

initiateFiles endp

;///////////////////////////////////////////////////////////////////////////////////////////////////////////
;in: bx - handler pliku to wczytywania
;out: al - znaki wczytane z pliku

getchar proc

	push cx
	push bx
	push dx
	
	xor ax,ax
	mov ax, word ptr ds:[BytesInBuf]	;czy w buforze sa jakies znaki?
	cmp ax, 0d
	ja takeFromBuffer		;jesli tak to bierz kolejny znak z bufora
	
	xor ah,ah
	mov ah, 3Fh				;jesli nie to uruchom funkcje 3Fh, ktora wczyta tyle znakow z BX(handler) ile wynosi CX
	mov cx, BUFSIZE
	mov dx, offset GetCharBuffer
	int 21h
	jc errorReading
	mov word ptr ds:[BytesInBuf], ax	;funkcja zwraca w ax faktyczna ilosc wczytanych znakow
	xor bx,bx
	mov word ptr ds:[Position], bx		;zeruje pozycje bufora
	
	takeFromBuffer:
		cmp ax, 0d				;czy pomimo tego ze bralismy znak z pliku to wczytalo ich zero?
		ja continueTaking		;jesli nie to kontynuuj
		mov al, EOF				;jesli tak to znaczy ze skonczyl sie plik wiec, zwroc EOF i wyjdz
		jmp getcharRet
		mov byte ptr ds:[Testing],al	;testuje czy dziala??
		
		continueTaking:
		push bx
		mov bx, word ptr ds:[Position]	;wczytaj ktory znak bufora teraz wczytujemy
		mov al, byte ptr ds:[GetCharBuffer+bx]
		pop bx
		dec word ptr ds:[BytesInBuf]
		inc word ptr ds:[Position]
		jmp getcharRet
	
	errorReading:
		mov ax, offset ErrorReadingFile
		call printString
		jmp exitCloseFiles
	
	getcharRet:	
		pop dx
		pop bx
		pop cx
		ret

getchar endp

;///////////////////////////////////////////////////////////////////////////////////////////////////////////
;zamyka pliki z ktorych korzystal program

closeFiles proc

	pusha
	
	mov ah, 3Eh			;funckja przerwania 21h ktora zamyka plik ktorego handle podajmey do bx
	mov bx, word ptr ds:[HandleIn1]
	int 21h
	jc errorClosing1	;jesli cf ustawiona to wystapil blad, ktory trzeba obsluzyc
	
	mov al, byte ptr ds:[Modification]		;jesli flaga modyfikacji nie jest ustawiona to przejdz od obslugi przypadku pierwsszego
	cmp al, 1d
	je SecondCase3
	
	mov ah, 3Eh			;przypadek pierwszy, zamykanie output
	mov bx, word ptr ds:[HandleOut]
	int 21h
	jc errorClosing3
	jmp ClosingFilesSucces
	
	SecondCase3:
		mov ah, 3Eh		;przypadek drugi, zamykaniu intput2
		mov bx, word ptr ds:[HandleIn2]
		int 21h
		jc errorClosing2
		jmp ClosingFilesSucces
	
	errorClosing1:
		mov ax, offset ErrorClosingInput1
		call printString
		jmp exitNormal
	
	errorClosing2:
		mov ax, offset ErrorClosingInput2
		call printString
		jmp exitNormal
		
	errorClosing3:
		mov ax, offset ErrorClosingOutput
		call printString
		jmp exitNormal
	
	ClosingFilesSucces:	
		popa
		ret

closeFiles endp

;////////////////////////////////////////////////////////////////////////////////////////////////////////////
;Wylicza CRC16 na podstawie pliku wejsciowego i zapisuje do pamieci

;MISCEL REFLECTED, source: http://miscel.dk/MiscEl/CRCcalculations.html

;CRC16 bit, inverted/reversed/reflected

;Remember to use corresponding polynomial values.
;function crc16reverse(Buffer:String;Polynom,Initial:Cardinal):Cardinal;
;var
;  i,j                   : Integer;
;begin
;Result:=Initial;
;for i:=1 to Length(Buffer) do begin
;  Result:=Result xor ord(buffer[i]);
;  for j:=0 to 7 do begin
;    if (Result and $0001)<>0 then Result:=(Result shr 1) xor Polynom
;    else Result:=Result shr 1;
;    end;
; end;
;end;

getCRC16 proc

	push bx
	push ax
	push dx
	push cx
	
	mov word ptr ds:[Position], 0d		;zeruj liczniki funkcji getchar
	mov word ptr ds:[BytesInBuf], 0d
	xor ax,ax							;zeruj wykorzystywane rejsetry
	xor bx,bx
	xor cx,cx
	xor dx,dx							;DX bedzie rejestrem przechowujacym CRC
	
	
	getCRCloop:
		push bx							;zapamietaj bx
		mov bx, word ptr ds:[HandleIn1]	;wczytaj do bx uchwyt pliku wejsciowego
		call getchar					;wczytaj kolejny znak
		pop bx
		xor ah,ah
		cmp al, EOF						;jesli to EOF to wychodzimy
		je finishCRC
		
		xor dx,ax						;xoruj znak do rejestru CRC

		mov cx,8d						;przchodzimy po 8 bitach w bajcie
		processByte:
			mov bx, dx
			and bx, 00001h
			cmp bx, 0d
			jne xoring
			shr dx, 1d
			loop processByte
			jmp getCRCloop				;jesli skonczy sie cx=8 to skocz do kolejnej iteracji petli po znakach
			xoring:
				shr dx,1d
				xor dx, Polynomial
				loop processByte
				jmp getCRCloop			;jesli skonczy sie cx=8 to skocz do kolejnej iteracji petli po znakach
	
	finishCRC:
		mov word ptr ds:[CRC1], dx		;zapisz rejestr CRC do pamieci
		pop cx
		pop dx
		pop ax
		pop bx
		ret

getCRC16 endp


;////////////////////////////////////////////////////////////////////////////////////////////////////
;in: al
;out: al
;odrwraca bity w bajcie

revByte proc

	push dx
	push cx
	push bx
	
	xor dx,dx
	mov cx, 8d
	revByteLoop:
		mov bl,al
		shl al, 1d
		and bl, 10000000b
		shr bl, cl
		or dl,bl
		loop revByteLoop
	
	mov al, dl
	pop bx
	pop cx
	pop dx
	ret

revByte endp

;////////////////////////////////////////////////////////////////////////////////////////////////
;in: ax
;out: ax
;odwraca bity w slowie

revCRC proc

	push bx
	push cx
	push dx
	
	xor dx,dx
	mov cx, 16d
	revCRCLoop:
		mov bx,ax
		shl ax, 1d
		and bx, 1000000000000000b
		shr bx, cl
		or dx, bx
		loop revCRCLoop
		
	mov ax, dx
	pop dx
	pop cx
	pop bx

revCRC endp

;////////////////////////////////////////////////////////////////////////////////////////////////////////////
;Zapisuje kod CRC do pliku wyjsciowego

saveCRC16 proc

	pusha
	 
	mov di, offset CRC1String		;zaladuj adres miejsca do ktorego bedziemy zapisywac string
	mov dx, word ptr ds:[CRC1]		;zaladuj obliczony kod CRC
	mov cx, 4d						;4 hexy do zapisania
	
	saveCrcLoop:
		rol dx, 4d					;rotuj 4 kolejne bity w lewo, (musze zapisywac string zaczynajac od czterach najstarszych bitow, 4 bity do zapisania bede trzymal na miejscu czterech najmlodszych)
		xor ax,ax					;wyczysz ax
		mov ax,dx					;zrob kopie dx w ax
		and ax,0000Fh				;interesuja mnie tylko 4 najmlodsze bity crc
		call convertBin				;zamien je na odpowiedni znak Ascii
		mov byte ptr ds:[di], al	;zapisz do pamieci
		inc di						;idz na kolejny znak
		loop saveCrcLoop
	
	mov ah,40h						;funkcja zapisujaca do pliku
	mov bx, word ptr ds:[HandleOut]	; w bx uchwyt pliku
	mov cx, 4d						;w cx ile bajtow ma zapisac
	mov dx, offset CRC1String		; w ds:dx offset stringu do zapisania
	int 21h
	jc errorSavingCRC				;jesli cf ustawione to obsluz blad
	
	mov ax, offset SavingSucces
	call printString
	jmp saveCRCret					;jesli nie to wroc z funckcji
	
	errorSavingCRC:
		mov ax, offset ErrorSaveCRC
		call printString
		jmp exitCloseFiles
		
	saveCRCret:
		popa
		ret

saveCRC16 endp

;////////////////////////////////////////////////////////////////////////////////////////////////////////////
;Wczytuje kod CRC drugiego pliku wejsciowego(w drugim przypadku), i porownuje z pierwszym kodem

checkCRC16 proc

	pusha
	xor dx,dx
	mov cl, 4d		;cztery znaki w zapisie heksadecymalnym liczby 16bitowej
	xor ax,ax
	mov word ptr ds:[Position], 0d		;zeruje liczniki funkji getchar
	mov word ptr ds:[BytesInBuf], 0d
	readCRC:
		mov bx, word ptr ds:[HandleIn2]
		call getchar		;pobierz znak z pliku
		cmp al, SPACE		;jesli to tab lub spacja to pomin
		je readCRC
		cmp al, TAB
		je readCRC
		cmp al, 10			;jesli to 10 lub 13 to tez pomin
		je readCRC
		cmp al,13
		je readCRC
		cmp al, EOF			;jesli to EOF to zglos blad, (z petli moge wyjsc tylko gdy cx dojdzie do zera)
		je errorChar
		
		cmp	al, '0'	;jesli numer mniejszy niz zera to na pewno zly znak
		jb	errorChar
		
		cmp al, ':'	;jesli numer mniejszy od tego co po dziewiatce a przeszedl poprzedni cmp to na pewno dobry znak, mozna isc dalej
		jb	OkByte1
		
		cmp al, 'A'	;jesli numer mnieszy niz A i przeszyly poprzednie porownania to na pewno zly znak
		jb	errorChar
		
		cmp al, 'G'	;jesli numer mniejszy od tego co po F i przeszly poprzednie porownania to na pewno dobry znak i mozna isc dalej
		jb	OkByte1
		
		cmp	al, 'a'	;j.w
		jb	errorChar
		
		cmp al, 'g'	;j.w.
		jb	OkByte1
		
		jmp errorChar
		
		OkByte1:
			call convertASCII		;zamien znak heksadecymalny na odpowiednia wartosc binarna
			xor ah,ah				;dla pewnosi wyzeruj ah
			shl dx, 4d				;zrob miejsce dla kolejnych czterech bitow ktore zaraz zostana dodane do sumy
			or dx, ax				;dodaj 4 nowe bity do sumy
			dec cl					;dekrementuj iterator petli
			cmp cl, 0d				;jesli zbadalem 4 znaki to kod sie skonczyl wiec skocz do sprawdzania zgodnosci CRC
			je EndReading
			jmp readCRC				;jesli nie to kontynnuj wczytywanie
			
		errorChar:					;blad formatu crc: zly znak lub za malo odpowiednich znakow
			mov ax, offset WrongCRC
			call printString
			jmp exitCloseFiles
		
		EndReading:					;sprawdz czy CRC sa zgodne
			cmp dx, word ptr ds:[CRC1]
			je CheckSucces
			
			mov ax, offset DifferentCRC
			call printString
			jmp exitCloseFiles
			
		CheckSucces:
			mov ax, offset SameCRC
			call printString
			jmp exitCloseFiles
	popa
	jmp exitCloseFiles

checkCRC16 endp

;/////////////////////////////////////////////////////////////////////////////////////////////////////////////

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

;///////////////////////////////////////////////////////////////////////////////////////////////////////////////
;zamienia 4 bitowa wartosc na odpowiedni znak hexowy
;in: al
;out: al

convertBin proc

	cmp al, 9d			;jesli ponizel 10 to na pewno zmienia na cyfre
	jbe digit
	
	add al, 55d			;odleglosc od 10 do A wynosi 55
	ret
	
	digit:
		add al,48d		;cyfry zaczynaja sie od 48
		ret
 
convertBin endp

;/////////////////////////////////////////////////////////////////////////////////////////////////////////////

changeMode proc

	mov al, byte ptr ds:[Modification]	;jesli flaga modyfikacji nie jest ustawiona to skocz do obslugi pierwszego przypadku, zapis kodu do pliku wyjsciowego
	cmp al, 0d
	je saveCRCjmp
	ret

changeMode endp

;//////////////////////////////////////////////////////////////////////////////////////////////////////////////

code1 ends

;************************STOS*******************************************************************************

stack1 segment stack
top dw ?
    dw 300 dup(?)	;602 bajtowy stos
stack1 ends

end start

;************************KONIEC******************************************************************************