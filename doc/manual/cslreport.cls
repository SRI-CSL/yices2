%% This is file cslreport.cls
%%
%% It has all the functionality of report class, with the following
%% changes:
%%  1. It generates a title page in the csl report style.
%%   - The default font is helvetica
%%   - It adds an \acknowledge command the contents of which are put
%%     next to the srilogo, as opposed to the \thanks which are footnotes.
%%  2 Defines \srilogo, which produces a graphic of the SRI Logo and
%%     adds it to the titlepage.
%%  3. It redefines \cleardoublepage to produce a plain pagestyle,
%%     and defines \cleardoublepageblank to produce an empty pagestyle
%%     on the even pages in twosided documents.
%%  4. A blank page after a part is pagestyle plain (was empty)
%%  5. The running headers and footers are not automatically uppercased
%%  6. (JMR) Defines \fpnote that puts extra material on the front page

\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{cslreport}[2001/04/05
 SRI Computer Science Lab report class]

\RequirePackage{graphicx}
\@ifundefined{pdfoutput}%
{\RequirePackage{color}}%
{\RequirePackage[pdftex,dvipsnames,usenames]{color}}%
\usepackage{helvetic}
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{report}}
\ProcessOptions
\LoadClass{report}

\textwidth 5.5in
\oddsidemargin .65in
\evensidemargin .41in

% Define the srilogo macro
\def\srilogo{\includegraphics[height=18mm]{srilogo}}
\def\srititle{\includegraphics[width=7in]{SRIInternational}}

% Font used for small font at the bottom of the titlepage
\font\sri@SRI=cmssbx10 scaled\magstep3%

\def\titlepagefooter{\newdimen\top@raise\newdimen\bot@raise%
  \hbox to 0pt{\raisebox{\bot@raise}[0pt]%
  {\vbox{\vspace*{100mm}%
  \hbox to 6.75in{{\@setsize\tiny{9}\viiipt\@viiipt\sf%Get us to 8pt for the following
  \hspace*{4mm}Computer Science Laboratory\hfill$\bullet$\hfill%
  333 Ravenswood Ave.\hfill$\bullet$\hfill Menlo Park, CA 94025\hfill$\bullet$\hfill%
  \ifx\telephonenum\undefined (650) 326-6200 %
                   \else \telephonenum{} \fi\hfill$\bullet$\hfill%
  % SRI's main FAX:  326-5512, division's 859-6171, AIC's 859-3735
  Facsimile: \ifx\faxphonenum\undefined (650) 859-2844 %
                             \else \faxphonenum{} \fi %
}}}}\hss}}

% Added \thispagestyle{plain}
\def\cleardoublepage{\clearpage\if@twoside \ifodd\c@page\else
    \hbox{}\thispagestyle{plain} 
    \newpage\if@twocolumn\hbox{}\newpage\fi\fi\fi}

\def\cleardoublepageblank{\clearpage\if@twoside \ifodd\c@page\else
    \hbox{}\thispagestyle{empty} 
    \newpage\if@twocolumn\hbox{}\newpage\fi\fi\fi}

\def\@endpart{\vfil\newpage
              \if@twoside
                \null
%                \thispagestyle{empty}%
                \thispagestyle{plain}%
                \newpage
              \fi
              \if@tempswa
                \twocolumn
              \fi}

\def\fpxnote#1{\gdef\@fpxnote{#1}}
\gdef\@fpxnote{}
\def\fpnote#1{\gdef\@fpnote{#1}}
\gdef\@fpnote{}
\def\acknowledge#1{\gdef\@acknowledge{#1}}
\gdef\@acknowledge{}
\newif\if@cslreportnumber
\def\cslreportnumber#1{\gdef\@cslreportnumber{#1}\@cslreportnumbertrue}
\gdef\@cslreportnumber{}

\renewenvironment{titlepage}
    {%
      \if@twocolumn
        \@restonecoltrue\onecolumn
      \else
        \@restonecolfalse\newpage
      \fi
      \thispagestyle{empty}%
      \setcounter{page}\@ne
    }%
    {\if@restonecol\twocolumn \else \newpage \fi
     \if@twoside\else
        \setcounter{page}\@ne
     \fi
    }

\def\and{%                  % \begin{tabular}
  \end{tabular}%
  \par%\hskip 1em \@plus.17fil%
  \begin{tabular}[t]{l}}%   % \end{tabular}

\newdimen\csltitle@topmargin
\newdimen\csltitle@leftmargin
\newdimen\csltitle@textwidth

\def\ps@myheadings{%
    \let\@oddfoot\@empty\let\@evenfoot\@empty
    \def\@evenhead{\thepage\hfil\slshape\leftmark}%
    \def\@oddhead{{\slshape\rightmark}\hfil\thepage}%
    \let\@mkboth\@gobbletwo
    \let\chaptermark\@gobble
    \let\sectionmark\@gobble
    }
  \if@titlepage
  \renewcommand\maketitle{%
  \begin{samepage}%
  \csltitle@leftmargin -\oddsidemargin
  \advance \csltitle@leftmargin by -.5in
  \hspace*{\csltitle@leftmargin}\parbox{7in}{\sffamily\begin{titlepage}%
  \let\footnotesize\small
  \let\footnoterule\relax
  \let \footnote \thanks
  \csltitle@topmargin -\topmargin
  \advance \csltitle@topmargin by -\headheight
  \advance \csltitle@topmargin by -\headsep
  \advance \csltitle@topmargin by -.5in
  \vspace*{\csltitle@topmargin}\noindent
  \csltitle@textwidth \textwidth
  \advance \csltitle@textwidth by \csltitle@leftmargin
  \srititle\par
  \vspace*{1.5in}\noindent
  {\color[gray]{0.5}\rule{7in}{1mm}}
  \begin{flushright}
    \if@cslreportnumber CSL Technical Report \@cslreportnumber\ $\bullet$ \fi
    \textsf{\@date}
  \end{flushright}
  \vspace*{.75in}
  \hspace*{1in}\raisebox{-.75in}[2in][0in]{\parbox{0in}{\rule{0pt}{6in}}\parbox[b]{6in}{%
  \begin{flushleft}%
    {\textsf{\LARGE \@title}\par}%
    \vskip 3em%
    {\large
     \lineskip .75em%
      \begin{tabular}[t]{l}%
        \@author
      \end{tabular}\par}%
      \vskip 1.5em%
      \ifx\@fpnote\@fpxnote\else \par\vspace*{3ex}\fbox{\parbox{\csltitle@textwidth}{\@fpnote}}\vspace*{1ex} \fi
  \end{flushleft}}}%
  \@thanks
  \nopagebreak[4]%
  \par\noindent\raisebox{-3.5in}[0pt][-4in]{\parbox{7in}{%
  \raisebox{-0.8cm}[1cm][1cm]{\srilogo}%
  \hspace*{1ex}\parbox{5in}{\small\@acknowledge}\vspace*{1ex}%
  \par\noindent\titlepagefooter}}%
  \end{titlepage}}%
  \end{samepage}%
  \setcounter{footnote}{0}%
  \global\let\thanks\relax
  \global\let\maketitle\relax
  \global\let\@thanks\@empty
  \global\let\@author\@empty
  \global\let\@date\@empty
  \global\let\@acknowledge\@empty
  \global\let\@fpnote\@empty
  \global\let\@title\@empty
  \global\let\title\relax
  \global\let\author\relax
  \global\let\date\relax
  \global\let\acknowledge\relax
  \global\let\fpnote\relax
  \global\let\and\relax
}
\else
\renewcommand\maketitle{\par
  \begingroup
    \renewcommand\thefootnote{\@fnsymbol\c@footnote}%
    \def\@makefnmark{\rlap{\@textsuperscript{\normalfont\@thefnmark}}}%
    \long\def\@makefntext##1{\parindent 1em\noindent
            \hb@xt@1.8em{%
                \hss\@textsuperscript{\normalfont\@thefnmark}}##1}%
    \if@twocolumn
      \ifnum \col@number=\@ne
        \@maketitle
      \else
        \twocolumn[\@maketitle]%
      \fi
    \else
      \newpage
      \global\@topnum\z@   % Prevents figures from going at top of page.
      \@maketitle
    \fi
    \thispagestyle{plain}\@thanks
  \endgroup
  \setcounter{footnote}{0}%
  \global\let\thanks\relax
  \global\let\maketitle\relax
  \global\let\@maketitle\relax
  \global\let\@thanks\@empty
  \global\let\@author\@empty
  \global\let\@date\@empty
  \global\let\@title\@empty
  \global\let\title\relax
  \global\let\author\relax
  \global\let\date\relax
  \global\let\and\relax
}
\def\@maketitle{%
  \newpage
  \null
  \vskip 2em%
  \begin{center}%
  \let \footnote \thanks
    {\LARGE \@title \par}%
    \vskip 1.5em%
    {\large
      \lineskip .5em%
      \begin{tabular}[t]{c}%
        \@author
      \end{tabular}\par}%
    \vskip 1em%
    {\large \@date}%
  \end{center}%
  \par
  \vskip 1.5em}
\fi

\if@twoside
  \def\ps@headings{%
      \let\@oddfoot\@empty\let\@evenfoot\@empty
      \def\@evenhead{\thepage\hfil\slshape\leftmark}%
      \def\@oddhead{{\slshape\rightmark}\hfil\thepage}%
      \let\@mkboth\markboth
    \def\chaptermark##1{%
%      \markboth {\MakeUppercase{%
%        \ifnum \c@secnumdepth >\m@ne
%            \@chapapp\ \thechapter. \ %
%        \fi
%        ##1}}{}}%
      \markboth {{%
        \ifnum \c@secnumdepth >\m@ne
            \@chapapp\ \thechapter. \ %
        \fi
        ##1}}{}}%
    \def\sectionmark##1{%
%      \markright {\MakeUppercase{%
%        \ifnum \c@secnumdepth >\z@
%          \thesection. \ %
%        \fi
%        ##1}}}}
      \markright {{%
        \ifnum \c@secnumdepth >\z@
          \thesection. \ %
        \fi
        ##1}}}}
\else
  \def\ps@headings{%
    \let\@oddfoot\@empty
    \def\@oddhead{{\slshape\rightmark}\hfil\thepage}%
    \let\@mkboth\markboth
    \def\chaptermark##1{%
%      \markright {\MakeUppercase{%
%        \ifnum \c@secnumdepth >\m@ne
%            \@chapapp\ \thechapter. \ %
%        \fi
%        ##1}}}}
      \markright {{%
        \ifnum \c@secnumdepth >\m@ne
            \@chapapp\ \thechapter. \ %
        \fi
        ##1}}}}
\fi

\renewcommand\tableofcontents{%
    \if@twocolumn
      \@restonecoltrue\onecolumn
    \else
      \@restonecolfalse
    \fi
%    \chapter*{\contentsname
%        \@mkboth{%
%           \MakeUppercase\contentsname}{\MakeUppercase\contentsname}}%
    \chapter*{\contentsname
        \@mkboth{%
           \contentsname}{\contentsname}}%
    \@starttoc{toc}%
    \if@restonecol\twocolumn\fi
    }

\renewcommand\listoffigures{%
    \if@twocolumn
      \@restonecoltrue\onecolumn
    \else
      \@restonecolfalse
    \fi
    \chapter*{\listfigurename
%      \@mkboth{\MakeUppercase\listfigurename}%
%              {\MakeUppercase\listfigurename}}%
      \@mkboth{\listfigurename}%
              {\listfigurename}}%
    \@starttoc{lof}%
    \if@restonecol\twocolumn\fi
    }

\renewcommand\listoftables{%
    \if@twocolumn
      \@restonecoltrue\onecolumn
    \else
      \@restonecolfalse
    \fi
    \chapter*{\listtablename
      \@mkboth{%
%          \MakeUppercase\listtablename}{\MakeUppercase\listtablename}}%
          \listtablename}{\listtablename}}%
    \@starttoc{lot}%
    \if@restonecol\twocolumn\fi
    }

\renewenvironment{thebibliography}[1]
     {\chapter*{\bibname
%        \@mkboth{\MakeUppercase\bibname}{\MakeUppercase\bibname}}%
        \@mkboth{\bibname}{\bibname}}%
      \list{\@biblabel{\@arabic\c@enumiv}}%
           {\settowidth\labelwidth{\@biblabel{#1}}%
            \leftmargin\labelwidth
            \advance\leftmargin\labelsep
            \@openbib@code
            \usecounter{enumiv}%
            \let\p@enumiv\@empty
            \renewcommand\theenumiv{\@arabic\c@enumiv}}%
      \sloppy\clubpenalty4000\widowpenalty4000%
      \sfcode`\.\@m}
     {\def\@noitemerr
       {\@latex@warning{Empty `thebibliography' environment}}%
      \endlist}

\renewenvironment{theindex}
               {\if@twocolumn
                  \@restonecolfalse
                \else
                  \@restonecoltrue
                \fi
                \columnseprule \z@
                \columnsep 35\p@
                \twocolumn[\@makeschapterhead{\indexname}]%
%                \@mkboth{\MakeUppercase\indexname}%
%                        {\MakeUppercase\indexname}%
                \@mkboth{\indexname}%
                        {\indexname}%
                \thispagestyle{plain}\parindent\z@
                \parskip\z@ \@plus .3\p@\relax
                \let\item\@idxitem}
               {\if@restonecol\onecolumn\else\clearpage\fi}
