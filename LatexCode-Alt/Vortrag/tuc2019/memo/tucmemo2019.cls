%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
% Hausmitteilungen nach dem Corporate Design 2019 der TU Chemnitz             %
% (c) Mario Haustein (mario.haustein@hrz.tu-chemnitz.de), 2014-2020           %
%                                                                             %
% Dieses Material steht unter der Creative-Commons-Lizenz Namensnennung -     %
% Keine Bearbeitungen 4.0 International. Um eine Kopie dieser Lizenz zu       %
% sehen, besuchen Sie http://creativecommons.org/licenses/by-nd/4.0/deed.de.  %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\ProvidesClass{tucmemo2019}[2024/01/31]

% Die restlichen Optionen an die Basisklasse weiterreichen.
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{tucletter2019}}

% Optionen verarbeiten.
\ProcessOptions*\relax

% Auf der KOMA-Script Briefklasse aufbauen.
\LoadClass{tucletter2019}

\RequirePackage{tabularx}
\RequirePackage[geometry]{ifsym}


% Adressfenster
\setplength{toaddrhpos}{25mm}
\setplength{toaddrvpos}{45mm}
\setplength{toaddrwidth}{90mm}
\setplength{toaddrheight}{55mm}	% 10mm größer für selbe Höhe wie Absenderergänzung
\setplength{backaddrheight}{0pt}

% Fußzeile (angepasst an Seitennummerierung)
\setplength{firstfootvpos}{286.4mm}	% 297mm - 10.6mm

% Betreff und nicht vorhandene Geschäftszeile
\setplength{refvpos}{103mm}		% 45mm + 45mm + 13mm
\setplength{refhpos}{25mm}
\setplength{refwidth}{165mm}		% 210mm - 25mm - 20mm
\setplength{refaftervskip}{0pt}
\setplength{subjectbeforevskip}{0pt}
\setplength{subjectaftervskip}{13.2pt}

% Absenderergänzung
\setplength{lochpos}{20mm}
\setplength{locvpos}{45mm}
\setplength{locwidth}{65mm}
\setplength{locheight}{55mm}		% 10mm größer, da sonst nicht hoch genug


% Kopfzeilen
\iftucenglish
\setkomavar{tucheadline1}{Internal memo}
\else
\setkomavar{tucheadline1}{Hausmitteilung}
\fi
\setkomavar{tucheadline2}{}
\setkomavar{tucheadline3}{}
\setkomavar{tucheadline4}{}

% Absenderadresse ausschalten.
\KOMAoptions{backaddress=off}

% Keine Ortsangabe
\AtBeginLetter{\setkomavar{place}{}}


% Anschrift
\newcommand{\m@keaddr}[2]{%
\setlength{\@tempdimc}{\useplength{toaddrwidth}}%
\addtolength{\@tempdimc}{-12mm}%
\mbox{\rule{0pt}{\f@size pt}%
\hbox to 12mm{#1:~\hfill}%
\parbox[t]{\@tempdimc}{\raggedright #2}}}

\newenvironment{memo}[2]%
{\setlength{\@tempdimc}{\useplength{toaddrheight}}%
\addtolength{\@tempdimc}{-1pt}%		% Warnungen vermeiden.
\letter{\mbox{\vbox to \@tempdimc{%
\parbox[t]{\useplength{toaddrwidth}}{%
\m@keaddr{An}{#1}\vspace{\baselineskip}
\m@keaddr{Von}{#2}}\vfill}}}}%
{\endletter}


% Ankreuzfelder
\newif\ifXrueckruf
\newif\ifXbearbeitung
\newif\ifXverbleib
\newif\ifXweiterleitung
\newif\ifXkenntnisnahme
\newif\ifXrueckgabe
\Xrueckruffalse
\Xbearbeitungfalse
\Xverbleibfalse
\Xweiterleitungfalse
\Xkenntnisnahmefalse
\Xrueckgabefalse


% Absenderergänzung
\newcommand{\mcbox}[1]{\raisebox{-0.3ex}{\rlap{#1}\Square}}%
\newcommand{\m@kecheckbox}[2]{\mcbox{\csname ifX#1\endcsname\Cross\fi}\hspace*{0.5em}\rule{0pt}{\f@size pt}#2}

\setkomavar{location}{%
\usekomafont{locfield}%
\fontsize{8pt}{11pt}\selectfont%
\hbox to 0pt{%
\begin{minipage}[t]{\hsize}
\vbox{%
\hbox{\begin{minipage}[t][32mm][t]{\hsize}
\@tempswafalse%
\m@kel@cline{myref}\Ifkomavarempty{myref}{\relax}{\@tempswatrue}%
\if@tempswa\vskip\baselineskip\fi%
\@tempswafalse%
\m@kel@cline{showname}%
\m@kel@cline{showloc}%
\m@kel@cline{showroom}%
\m@kel@cline{showphone}%
\m@kel@cline{showfax}%
\m@kel@cline{showemail}%
\newkomavar{dateplace}
\setkomavar{dateplace}{\Ifkomavarempty{place}{\relax}{\usekomavar{place}\usekomavar{placeseparator}}\usekomavar{date}}
\setkomavar*{dateplace}{\Ifkomavarempty{place}{\relax}{\Ifkomavarempty*{place}{\relax}{\usekomavar*{place},~}}\usekomavar*{date}}
\Ifkomavarempty{date}{\setkomavar{dateplace}[]{}}{\relax}
\Ifkomavarempty*{date}{\setkomavar*{dateplace}{}}{\relax}
\m@kel@cline{dateplace}%
\end{minipage}}%
\vspace{\baselineskip}
\hbox{\begin{minipage}[c]{\hsize}
\iftucenglish
\par\textbf{Internal memo with request to:}
\else
\par\textbf{Kurzmitteilung mit der Bitte um:}
\fi\\
\begin{tabularx}{\linewidth}{@{}p{30mm}@{}X}
\iftucenglish
\m@kecheckbox{rueckruf}{callback}           &
\m@kecheckbox{weiterleitung}{forward}       \\
\m@kecheckbox{bearbeitung}{process}         &
\m@kecheckbox{kenntnisnahme}{take notice}   \\
\m@kecheckbox{verbleib}{remain}             &
\m@kecheckbox{rueckgabe}{return}            \\
\else
\m@kecheckbox{rueckruf}{R\"uckruf}          &
\m@kecheckbox{weiterleitung}{Weiterleitung} \\
\m@kecheckbox{bearbeitung}{Bearbeitung}     &
\m@kecheckbox{kenntnisnahme}{Kenntnisnahme} \\
\m@kecheckbox{verbleib}{Verbleib}           &
\m@kecheckbox{rueckgabe}{R\"uckgabe}        \\
\fi
\end{tabularx}
\end{minipage}}}%
\end{minipage}\hss}}


% Keine Fußzeile
\setkomavar{firstfoot}{}


\endinput
