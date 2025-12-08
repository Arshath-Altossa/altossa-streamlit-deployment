# Altossa Product Selector & Visualizer

![Streamlit](https://img.shields.io/badge/Streamlit-FF4B4B?style=for-the-badge&logo=Streamlit&logoColor=white) ![Python](https://img.shields.io/badge/Python-3776AB?style=for-the-badge&logo=python&logoColor=white) ![PostgreSQL](https://img.shields.io/badge/PostgreSQL-316192?style=for-the-badge&logo=postgresql&logoColor=white) ![Status](https://img.shields.io/badge/Status-Production-success?style=for-the-badge)

**Altossa Selector** is a comprehensive internal tool designed for interior design professionals and sales teams. It streamlines the process of selecting furniture, generating visual room layouts, creating pro-forma invoices, and tracking order history.

---

## Key Features

### Product Selection & Catalog
* **Room-First Browsing**: Navigate products by specific rooms (Living Room, Bedroom, Dining, etc.) or browse by product categories (Sofas, Armchairs, Beds).
* **Smart Filtering**: Advanced filtering by **Brand**, **Price Range**, and **Product Name**.
* **Dynamic Pricing**: Automatic price calculations based on brand multipliers and category selections (Fabric/Leather/Other).
* **Variant Management**: Select specific sizes, materials, and subtypes for every product.

### Visual Exports & Reporting
* **Room Visualizers**: Automatically generates PDF visual layouts for:
    * Drawing Room
    * Living Room
    * Bedrooms (1, 2, 3)
    * Dining Room & Others
* **Pro-forma Invoices**: Generates professional PDF invoices with editable pricing overrides for negotiations.
* **PPT Export**: Exports selected items into a PowerPoint presentation for client pitches.
* **Excel Export**: Download the full selection list as a detailed spreadsheet.

### Order Management & Admin
* **Wallet & History**: Tracks total sales volume and wallet balance with a ledger for Credits/Debits.
* **Admin Dashboard**: A secure, password-protected backend to **Add**, **Edit**, or **Delete** products directly from the UI without touching the database.
* **Persistent Cart**: Auto-saves your selection state, allowing you to close the tab and resume later.

---

## Tech Stack

| Component | Technology |
| :--- | :--- |
| **Frontend** | ![Streamlit](https://img.shields.io/badge/-Streamlit-FF4B4B?logo=streamlit&logoColor=white) |
| **Backend Logic** | ![Python](https://img.shields.io/badge/-Python-3776AB?logo=python&logoColor=white) |
| **Database** | ![PostgreSQL](https://img.shields.io/badge/-PostgreSQL-336791?logo=postgresql&logoColor=white) & ![SQLite](https://img.shields.io/badge/-SQLite-003B57?logo=sqlite&logoColor=white) |
| **Data Processing** | ![Pandas](https://img.shields.io/badge/-Pandas-150458?logo=pandas&logoColor=white) ![NumPy](https://img.shields.io/badge/-NumPy-013243?logo=numpy&logoColor=white) |
| **PDF Generation** | `ReportLab`, `PyPDF` |
| **Security** | `Bcrypt`, `Hashlib` |

---

## ⚙️ Installation & Setup

Follow these steps to run the application locally.

### 1. Clone the Repository
```bash
git clone [https://github.com/Arshath-Altossa/altossa-selector.git](https://github.com/Arshath-Altossa/altossa-selector.git)
cd altossa-selector
```

### 2. Set up Environment
Create a virtual environment and install dependencies.
```bash
python -m venv venv
# Windows
venv\Scripts\activate
# Mac/Linux
source venv/bin/activate

pip install -r requirements.txt
```

### 3. Configure Secrets
Create a .env file in the root directory. Do not commit this file.
```bash
python -m venv venv
# Windows
venv\Scripts\activate
# Mac/Linux
source venv/bin/activate

pip install -r requirements.txt
```

### 4. Run the App
```bash
streamlit run app.py
```

## Project Structure
```bash
altossa-selector/
├── app.py                 # Main application entry point
├── requirements.txt       # Python dependencies
├── .env                   # Environment variables (Ignored by Git)
├── template/              # Background templates for PDF generation
│   ├── drawing_room_base.png
│   ├── living_room_base.png
│   ├── bedroom_base.png
│   └── dining_room_base.png
├── .altossa_state/        # Local persistent state storage
└── .altossa_attachments/  # Local image cache storage
```

## Contact & Author
AI Team - Altossa